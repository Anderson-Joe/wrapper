#include "lite.h"
#include "import.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <mutex>
#include <chrono>
#include <cctype>
#include <thread>
#include <atomic>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
#include <pthread.h>
#include "cJSON.h"
#include "logger.h"

/* ---- httplib.h (header-only HTTP server) ---- */
/* NDK API 22 does not declare getifaddrs in headers, but it is available at runtime */
/* Provide stub implementations (never called since we bind to a fixed host) */
#include <ifaddrs.h>
extern "C" int getifaddrs(struct ifaddrs** __list_ptr) { return -1; }
extern "C" void freeifaddrs(struct ifaddrs* __ptr) { }
#ifndef CPPHTTPLIB_THREAD_POOL_COUNT
#define CPPHTTPLIB_THREAD_POOL_COUNT 8
#endif
#include "httplib.h"

/* ---- Configuration ---- */
static std::string g_host = "127.0.0.1";
static int g_port = 12340;
static bool g_login_only = false;
static std::string g_login_credentials;
static std::string g_proxy;
/* Device info: <client>/<version>/<platform>/<osver>/<model>/<build>/<locale>/<lang>/<android-id>.
   The Android ID is derived from the account username (hashed) and persisted so
   each account keeps a stable device identity; without a username the persisted
   ID (or a default) is used. */
static std::string g_device_info_prefix = "Music/5.0.2/Android/10/Pixel 8/7663314/en-US/en-US";
static std::string g_default_android_id = "e82320052964d21a";
static std::string g_device_info_override;
static std::string g_resolved_device_info;
static std::string g_base_dir = "data";
static std::string g_log_level = "info";
static std::string g_log_file;
static int g_token_refresh_interval = 1800;
static bool g_cors_enabled = false;
static std::string g_dns_servers;
static std::string g_ca_bundle;

/* ---- Token state and background refresh ---- */
static std::mutex g_tokens_mutex;
static std::string g_web_dev_token;
static std::chrono::steady_clock::time_point g_last_web_dev_attempt;
static std::atomic<bool> g_refresh_stop{false};
static httplib::Server* g_svr = nullptr;
static sigset_t g_signal_set;

struct WebTokens {
    std::string dev_token;
    std::string music_token;
    std::string storefront_id;
    bool valid() const { return !dev_token.empty() && !music_token.empty(); }
};

/* ============================== */
/*     JSON helpers (cJSON)       */
/* ============================== */

static std::string json_dump(cJSON* root) {
    char* p = cJSON_PrintUnformatted(root);
    if (!p) return "{}";
    std::string s(p);
    cJSON_free(p);
    return s;
}

static std::string json_success(cJSON* data) {
    cJSON* root = cJSON_CreateObject();
    cJSON_AddNumberToObject(root, "code", 0);
    cJSON_AddStringToObject(root, "msg", "SUCCESS");
    if (data) cJSON_AddItemToObject(root, "data", data);
    else cJSON_AddNullToObject(root, "data");
    std::string s = json_dump(root);
    cJSON_Delete(root);
    return s;
}

static std::string json_error(int code, const std::string& msg) {
    cJSON* root = cJSON_CreateObject();
    cJSON_AddNumberToObject(root, "code", code);
    cJSON_AddStringToObject(root, "msg", msg.c_str());
    std::string s = json_dump(root);
    cJSON_Delete(root);
    return s;
}

#include "storefront_ids.inc"

/* The Android lib writes storefront identifiers like "143462-1,31"; the Apple
 * Music web API expects a two-letter country code ("jp").  Unknown IDs map to
 * the empty string (not a made-up default) so /status reflects whether the
 * account is actually logged in. */
static std::string normalize_storefront_id(const std::string& raw) {
    if (raw.empty()) return "";
    if (raw.size() == 2 && std::isalpha((unsigned char)raw[0]) &&
        std::isalpha((unsigned char)raw[1])) {
        return raw;
    }
    std::string first = raw.substr(0, raw.find('-'));
    return builtin_storefront_region(first);
}

/* ---- Device info / Android ID ---- */

static std::string hash_android_id(const std::string& username) {
    uint64_t h = 1469598103934665603ULL; /* FNV-1a 64-bit offset basis */
    for (unsigned char c : username) {
        h ^= c;
        h *= 1099511628211ULL;
    }
    char buf[17];
    snprintf(buf, sizeof(buf), "%016llx", (unsigned long long)h);
    return std::string(buf);
}

static std::string resolve_device_info(const std::string& username) {
    if (!g_device_info_override.empty()) return g_device_info_override;

    std::string androidId;
    if (!username.empty()) {
        androidId = hash_android_id(username);
        /* persist so service mode (which has no username) can reuse it */
        std::string path = g_base_dir + "/ANDROID_ID";
        FILE* f = fopen(path.c_str(), "w");
        if (f) {
            fwrite(androidId.c_str(), 1, androidId.size(), f);
            fclose(f);
        }
    } else {
        std::string path = g_base_dir + "/ANDROID_ID";
        std::ifstream f(path);
        if (f) {
            std::string c((std::istreambuf_iterator<char>(f)),
                          std::istreambuf_iterator<char>());
            while (!c.empty() && (c.back() == ' ' || c.back() == 10 || c.back() == 13)) c.pop_back();
            if (!c.empty()) androidId = c;
        }
        if (androidId.empty()) androidId = g_default_android_id;
    }
    return g_device_info_prefix + "/" + androidId;
}

/* ============================== */
/*     Token cache helpers        */
/* ============================== */

static void load_token_cache() {
    std::lock_guard<std::mutex> lock(g_tokens_mutex);
    g_tokens.base_dir = g_base_dir;
    g_tokens.load();
    if (g_tokens.music_token.empty()) g_tokens.music_token = get_music_token();
    if (g_tokens.storefront_id.empty()) g_tokens.storefront_id = get_storefront();
    g_tokens.storefront_id = normalize_storefront_id(g_tokens.storefront_id);
    /* leave storefront empty when not logged in; do not invent "us" */
}

/* Caller must hold g_tokens_mutex. */
static void save_token_cache() {
    g_tokens.base_dir = g_base_dir;
    g_tokens.save();
}

/* Fetch dev token for Lyrics/License/WebPlayback.  The web endpoints must use
 * the WebPlay dev token embedded in music.apple.com's JS (iss=AMPWebPlay,
 * kid=WebPlayKid) - exactly what wrapper-manager's GetToken() returns and the
 * token the browser sends.  The Android storeservicescore token
 * (iss=UDK28SN10P) is accepted by webPlayback and lyrics but REJECTED by
 * acquireWebPlaybackLicense (Apple returns HTTP 500), so it is only a
 * fallback when the scrape is unavailable. */
static WebTokens get_web_tokens() {
    std::lock_guard<std::mutex> lock(g_tokens_mutex);
    if (g_tokens.music_token.empty()) g_tokens.music_token = get_music_token();
    if (g_tokens.storefront_id.empty()) g_tokens.storefront_id = get_storefront();
    g_tokens.storefront_id = normalize_storefront_id(g_tokens.storefront_id);
    /* leave storefront empty when not logged in; do not invent "us" */

    auto now = std::chrono::steady_clock::now();
    if (g_web_dev_token.empty()) {
        /* retry the scrape at most every 60 s until it succeeds */
        if (g_last_web_dev_attempt == std::chrono::steady_clock::time_point{} ||
            now - g_last_web_dev_attempt > std::chrono::seconds(60)) {
            g_last_web_dev_attempt = now;
            g_web_dev_token = AppleApi::getDevToken();
        }
    } else if (now - g_last_web_dev_attempt > std::chrono::hours(24)) {
        /* refresh the long-lived WebPlay token once a day (wrapper-manager) */
        g_last_web_dev_attempt = now;
        std::string fresh = AppleApi::getDevToken();
        if (!fresh.empty()) g_web_dev_token = fresh;
    }

    WebTokens tokens;
    tokens.dev_token = g_web_dev_token.empty() ? g_tokens.dev_token : g_web_dev_token;
    tokens.music_token = g_tokens.music_token;
    tokens.storefront_id = g_tokens.storefront_id;
    return tokens;
}

/* ---- b64 encode (for ctx/state) ---- */
static std::string b64_encode(const uint8_t* data, size_t len) {
    static const char* tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    std::string out;
    out.reserve(((len + 2) / 3) * 4);
    for (size_t i = 0; i < len; i += 3) {
        uint32_t n = data[i] << 16;
        if (i + 1 < len) n |= data[i + 1] << 8;
        if (i + 2 < len) n |= data[i + 2];
        out += tbl[(n >> 18) & 0x3f];
        out += tbl[(n >> 12) & 0x3f];
        out += (i + 1 < len) ? tbl[(n >> 6) & 0x3f] : '=';
        out += (i + 2 < len) ? tbl[n & 0x3f] : '=';
    }
    return out;
}


/* ============================== */
/*     HTTP Handlers              */
/* ============================== */

static bool valid_catalog_language(const std::string& language) {
    return language.empty() || (language.size() <= 64 && language.front() != '-' &&
        language.back() != '-' && language.find("--") == std::string::npos &&
        language.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-") ==
            std::string::npos);
}

static int catalog_language_status(const std::string& region, const std::string& language,
                                   const std::string& devToken) {
    if (language.empty()) return 200;
    using Clock = std::chrono::steady_clock;
    struct StorefrontLanguages {
        std::vector<std::string> tags;
        Clock::time_point expires;
    };
    static std::mutex cacheMutex;
    static std::map<std::string, StorefrontLanguages> cache;
    const auto statusFor = [&](const std::vector<std::string>& tags) {
        return std::find(tags.begin(), tags.end(), language) != tags.end() ? 200 : 400;
    };
    {
        std::lock_guard<std::mutex> lock(cacheMutex);
        const auto entry = cache.find(region);
        if (entry != cache.end() && entry->second.expires > Clock::now()) {
            return statusFor(entry->second.tags);
        }
    }

    std::string body;
    const long status = AppleApi::getCatalogResponse("/v1/storefronts/" + region, devToken, body);
    if (status != 200) return status == 429 ? 429 : 502;
    cJSON* root = cJSON_Parse(body.c_str());
    const auto* item = cJSON_GetArrayItem(cJSON_GetObjectItemCaseSensitive(root, "data"), 0);
    const auto* id = cJSON_GetObjectItemCaseSensitive(item, "id");
    const auto* attrs = cJSON_GetObjectItemCaseSensitive(item, "attributes");
    const auto* tags = cJSON_GetObjectItemCaseSensitive(attrs, "supportedLanguageTags");
    StorefrontLanguages entry{{}, Clock::now() + std::chrono::hours(1)};
    if (cJSON_IsString(id) && region == id->valuestring && cJSON_IsArray(tags)) {
        const cJSON* tag = nullptr;
        cJSON_ArrayForEach(tag, tags) {
            if (cJSON_IsString(tag)) entry.tags.emplace_back(tag->valuestring);
        }
    }
    cJSON_Delete(root);
    if (entry.tags.empty()) return 502;
    const int result = statusFor(entry.tags);
    std::lock_guard<std::mutex> lock(cacheMutex);
    cache[region] = std::move(entry);
    return result;
}

static const char* catalog_language_error(int status) {
    if (status == 400) return "invalid catalog language";
    if (status == 429) return "catalog rate limit reached";
    return "catalog storefront language lookup failed";
}

static const cJSON* song_search_album(const cJSON* song, const cJSON* songAttrs) {
    const cJSON* relationships = cJSON_GetObjectItemCaseSensitive(song, "relationships");
    const cJSON* albums = cJSON_GetObjectItemCaseSensitive(relationships, "albums");
    const cJSON* items = cJSON_GetObjectItemCaseSensitive(albums, "data");
    const int count = cJSON_GetArraySize(items);
    if (!cJSON_IsArray(items) || count == 0) return nullptr;
    if (count == 1) {
        return cJSON_GetArrayItem(items, 0);
    }

    // 多个关联版本时，只使用与搜索结果的所属专辑名唯一对应的版本。
    const cJSON* expected = cJSON_GetObjectItemCaseSensitive(songAttrs, "albumName");
    if (!cJSON_IsString(expected)) return nullptr;
    const cJSON* match = nullptr;
    const cJSON* album = nullptr;
    cJSON_ArrayForEach(album, items) {
        const cJSON* attrs = cJSON_GetObjectItemCaseSensitive(album, "attributes");
        const cJSON* name = cJSON_GetObjectItemCaseSensitive(attrs, "name");
        if (cJSON_IsString(name) && std::string(name->valuestring) == expected->valuestring) {
            if (match) return nullptr;
            match = album;
        }
    }
    return match;
}

static void add_search_track_count(cJSON* hit, const cJSON* attrs, const char* field) {
    const cJSON* count = cJSON_GetObjectItemCaseSensitive(attrs, "trackCount");
    if (cJSON_IsNumber(count) && count->valueint >= 0 && count->valuedouble == count->valueint) {
        cJSON_AddNumberToObject(hit, field, count->valueint);
    }
}

static void handle_catalog_search(const httplib::Request& req, httplib::Response& res) {
    const auto fail = [&](int status, const char* message) {
        res.status = status;
        res.set_content(json_error(status, message), "application/json");
    };
    const auto number = [&](const char* key, int fallback, int max) {
        if (!req.has_param(key)) return fallback;
        const auto value = req.get_param_value(key);
        if (value.empty() || value.size() > 6 ||
            value.find_first_not_of("0123456789") != std::string::npos) return -1;
        const int result = std::atoi(value.c_str());
        return result <= max ? result : -1;
    };

    const auto term = req.get_param_value("term");
    const auto type = req.get_param_value("type");
    const auto language = req.get_param_value("language");
    if (!valid_catalog_language(language)) {
        fail(400, "invalid catalog language");
        return;
    }
    const int limit = number("limit", 20, 25);
    const int offset = number("offset", 0, 10000);
    std::string region = req.get_param_value("region");
    if (term.empty() || term.size() > 512 || term.find_first_not_of(" \t\r\n") == std::string::npos ||
        (type != "songs" && type != "albums") || limit < 1 || offset < 0 ||
        (req.has_param("region") && (region.size() != 2 ||
         region.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") != std::string::npos))) {
        fail(400, "invalid catalog search parameters");
        return;
    }

    std::string devToken;
    {
        std::lock_guard<std::mutex> lock(g_tokens_mutex);
        if (!req.has_param("region")) region = normalize_storefront_id(g_tokens.storefront_id);
        devToken = g_tokens.dev_token;
    }
    if (region.empty() || devToken.empty()) {
        fail(503, "catalog session unavailable");
        return;
    }
    std::transform(region.begin(), region.end(), region.begin(), [](unsigned char ch) {
        return static_cast<char>(std::tolower(ch));
    });

    const int languageStatus = catalog_language_status(region, language, devToken);
    if (languageStatus != 200) {
        fail(languageStatus, catalog_language_error(languageStatus));
        return;
    }
    std::string body;
    const long status = AppleApi::searchCatalog(region, term, type, limit, offset, language, devToken, body);
    if (status == 400 && !language.empty()) {
        fail(400, "invalid catalog language");
        return;
    }
    if (status == 401 || status == 403) {
        fail(502, "catalog authorization rejected");
        return;
    }
    if (status == 429) {
        fail(429, "catalog rate limit reached");
        return;
    }
    if (status != 200) {
        fail(502, "catalog request failed");
        return;
    }

    cJSON* root = cJSON_Parse(body.c_str());
    const cJSON* results = cJSON_GetObjectItemCaseSensitive(root, "results");
    const cJSON* group = cJSON_GetObjectItemCaseSensitive(results, type.c_str());
    const cJSON* items = cJSON_GetObjectItemCaseSensitive(group, "data");
    if (!cJSON_IsObject(results) || (group && !cJSON_IsArray(items))) {
        cJSON_Delete(root);
        fail(502, "invalid catalog response");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    cJSON_AddStringToObject(data, "region", region.c_str());
    if (!language.empty()) cJSON_AddStringToObject(data, "language", language.c_str());
    cJSON_AddBoolToObject(data, "hasNext",
                          cJSON_IsString(cJSON_GetObjectItemCaseSensitive(group, "next")));
    cJSON* hits = cJSON_AddArrayToObject(data, "items");
    const cJSON* item = nullptr;
    cJSON_ArrayForEach(item, items) {
        const cJSON* attrs = cJSON_GetObjectItemCaseSensitive(item, "attributes");
        const cJSON* id = cJSON_GetObjectItemCaseSensitive(item, "id");
        const cJSON* name = cJSON_GetObjectItemCaseSensitive(attrs, "name");
        if (!cJSON_IsString(id) || !cJSON_IsString(name)) continue;
        cJSON* hit = cJSON_CreateObject();
        cJSON_AddItemToArray(hits, hit);
        cJSON_AddStringToObject(hit, "id", id->valuestring);
        for (const char* field : {"name", "artistName", "albumName", "releaseDate", "url"}) {
            const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
            if (cJSON_IsString(value)) cJSON_AddStringToObject(hit, field, value->valuestring);
        }
        if (type == "albums") {
            add_search_track_count(hit, attrs, "trackCount");
        } else if (const cJSON* albumItem = song_search_album(item, attrs)) {
            const cJSON* albumId = cJSON_GetObjectItemCaseSensitive(albumItem, "id");
            if (cJSON_IsString(albumId)) cJSON_AddStringToObject(hit, "albumId", albumId->valuestring);
            const cJSON* album = cJSON_GetObjectItemCaseSensitive(albumItem, "attributes");
            add_search_track_count(hit, album, "albumTrackCount");
            const cJSON* releaseDate = cJSON_GetObjectItemCaseSensitive(album, "releaseDate");
            if (cJSON_IsString(releaseDate)) {
                cJSON_AddStringToObject(hit, "albumReleaseDate", releaseDate->valuestring);
            }
            const cJSON* albumName = cJSON_GetObjectItemCaseSensitive(album, "name");
            if (cJSON_IsString(albumName) && !cJSON_GetObjectItemCaseSensitive(hit, "albumName")) {
                cJSON_AddStringToObject(hit, "albumName", albumName->valuestring);
            }
        }
    }
    cJSON_Delete(root);
    res.set_content(json_success(data), "application/json");
}

enum class CatalogLookup { Item, AlbumTracks, SongMusicVideos };

static void handle_catalog_detail(const httplib::Request& req, httplib::Response& res, CatalogLookup lookup) {
    const bool tracks = lookup == CatalogLookup::AlbumTracks;
    const bool relatedVideos = lookup == CatalogLookup::SongMusicVideos;
    const bool collection = lookup != CatalogLookup::Item;
    const auto fail = [&](int status, const char* message) {
        res.status = status;
        res.set_content(json_error(status, message), "application/json");
    };
    const auto id = req.get_param_value("id");
    const auto language = req.get_param_value("language");
    if (!valid_catalog_language(language)) {
        fail(400, "invalid catalog language");
        return;
    }
    auto region = req.get_param_value("region");
    const auto type = tracks ? std::string("albums")
                    : relatedVideos ? std::string("songs") : req.get_param_value("type");
    const auto offset = req.has_param("offset") ? req.get_param_value("offset") : "0";
    if (id.empty() || id.size() > 20 || id.find_first_not_of("0123456789") != std::string::npos ||
        region.size() != 2 ||
        region.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") != std::string::npos ||
        (type != "songs" && type != "albums" && type != "artists" && type != "music-videos") ||
        offset.empty() || offset.size() > 5 ||
        offset.find_first_not_of("0123456789") != std::string::npos) {
        fail(400, "invalid catalog lookup parameters");
        return;
    }
    std::transform(region.begin(), region.end(), region.begin(), [](unsigned char ch) {
        return static_cast<char>(std::tolower(ch));
    });
    std::string devToken;
    {
        std::lock_guard<std::mutex> lock(g_tokens_mutex);
        devToken = g_tokens.dev_token;
    }
    if (devToken.empty()) {
        fail(503, "catalog session unavailable");
        return;
    }
    const int languageStatus = catalog_language_status(region, language, devToken);
    if (languageStatus != 200) {
        fail(languageStatus, catalog_language_error(languageStatus));
        return;
    }
    std::string path = "/v1/catalog/" + region + "/" + type + "/" + id;
    if (tracks) path += "/tracks?limit=25&offset=" + offset;
    if (relatedVideos) {
        path += "/music-videos";
        // Apple 的歌曲关联 MV 使用自己的分页大小。
        if (offset.find_first_not_of('0') != std::string::npos) path += "?offset=" + offset;
    }

    const bool musicVideo = type == "music-videos" || relatedVideos;
    const bool metadata = req.get_param_value("metadata") == "1" && !collection;
    const bool include = metadata && type != "artists";
    const bool artistMotion = !collection && type == "artists" && req.get_param_value("artistMotion") == "1";
    const bool albumMotion = !collection && type == "albums" && req.get_param_value("albumMotion") == "1";
    const bool motion = artistMotion || albumMotion;
    if (include) {
        if (type == "songs") path += "?include=albums,artists,composers,credits,genres";
        else if (musicVideo) path += "?include=albums,artists,genres,songs";
        else path += "?include=artists";
    }
    if (motion) path += include ? "&extend=editorialVideo" : "?extend=editorialVideo";
    if (!language.empty()) {
        path += path.find('?') != std::string::npos ? "&l=" : "?l=";
        path += language;
    }

    std::string body;
    const long status = AppleApi::getCatalogResponse(path, devToken, body);
    if (relatedVideos && status == 204) body = "{\"data\":[]}";
    if (status == 400 && !language.empty()) {
        fail(400, "invalid catalog language");
        return;
    }
    if (status == 401 || status == 403) {
        fail(502, "catalog authorization rejected");
        return;
    }
    if (status == 404) {
        fail(404, "catalog resource not found");
        return;
    }
    if (status == 429) {
        fail(429, "catalog rate limit reached");
        return;
    }
    if (status != 200 && !(relatedVideos && status == 204)) {
        fail(502, "catalog request failed");
        return;
    }

    cJSON* root = cJSON_Parse(body.c_str());
    const cJSON* upstreamItems = cJSON_GetObjectItemCaseSensitive(root, "data");
    const cJSON* upstreamNext = cJSON_GetObjectItemCaseSensitive(root, "next");
    if (!cJSON_IsArray(upstreamItems) || (upstreamNext && !cJSON_IsString(upstreamNext))) {
        cJSON_Delete(root);
        fail(502, "invalid catalog response");
        return;
    }
    if (!collection && cJSON_GetArraySize(upstreamItems) == 0) {
        cJSON_Delete(root);
        fail(404, "catalog resource not found");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    if (motion) cJSON_AddBoolToObject(data, artistMotion ? "artistMotionSupported" : "albumMotionSupported", true);
    if (relatedVideos) cJSON_AddStringToObject(data, "songId", id.c_str());
    if (!language.empty()) cJSON_AddStringToObject(data, "language", language.c_str());
    cJSON* items = cJSON_AddArrayToObject(data, "items");
    const cJSON* item = nullptr;
    cJSON_ArrayForEach(item, upstreamItems) {
        const cJSON* attrs = cJSON_GetObjectItemCaseSensitive(item, "attributes");
        const cJSON* itemId = cJSON_GetObjectItemCaseSensitive(item, "id");
        const cJSON* itemType = cJSON_GetObjectItemCaseSensitive(item, "type");
        const cJSON* name = cJSON_GetObjectItemCaseSensitive(attrs, "name");
        if (!cJSON_IsString(itemId) || !cJSON_IsString(itemType) || !cJSON_IsString(name) ||
            (musicVideo && (strcmp(itemType->valuestring, "music-videos") != 0 ||
                            (!relatedVideos && id != itemId->valuestring)))) {
            cJSON_Delete(root);
            cJSON_Delete(data);
            fail(502, "invalid catalog response");
            return;
        }
        cJSON* hit = cJSON_CreateObject();
        cJSON_AddItemToArray(items, hit);
        cJSON_AddStringToObject(hit, "id", itemId->valuestring);
        cJSON_AddStringToObject(hit, "type", itemType->valuestring);
        cJSON_AddStringToObject(hit, "name", name->valuestring);
        const cJSON* video = cJSON_GetObjectItemCaseSensitive(attrs, "editorialVideo");
        if (motion && cJSON_IsObject(video)) {
            cJSON* variants = cJSON_AddObjectToObject(hit, "editorialVideo");
            const std::initializer_list<const char*> artistFields = {
                "motionArtistSquare1x1", "motionArtistWide16x9", "motionArtistFullscreen16x9"
            };
            const std::initializer_list<const char*> albumFields = {"motionDetailSquare", "motionDetailTall"};
            for (const char* field : artistMotion ? artistFields : albumFields) {
                const cJSON* entry = cJSON_GetObjectItemCaseSensitive(video, field);
                if (cJSON_IsObject(entry)) cJSON_AddItemToObject(variants, field, cJSON_Duplicate(entry, true));
            }
        }
        if (type == "artists") {
            for (const char* field : {"artwork", "editorialNotes", "genreNames", "url"}) {
                const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
                if (value) cJSON_AddItemToObject(hit, field, cJSON_Duplicate(value, true));
            }
            continue;
        }
        for (const char* field : {"artistName", "albumName"}) {
            const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
            if (cJSON_IsString(value)) cJSON_AddStringToObject(hit, field, value->valuestring);
        }
        for (const char* field : {"discNumber", "trackNumber", "trackCount"}) {
            const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
            if (cJSON_IsNumber(value)) cJSON_AddNumberToObject(hit, field, value->valuedouble);
        }
        if (musicVideo) {
            for (const char* field : {"releaseDate", "durationInMillis", "isrc", "url", "has4K", "hasHDR",
                                      "artwork", "genreNames", "contentRating", "editorialNotes", "previews",
                                      "playParams", "videoSubType", "artistUrl", "workId", "workName"}) {
                const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
                if (value) cJSON_AddItemToObject(hit, field, cJSON_Duplicate(value, true));
            }
        }
        if (metadata && !musicVideo) {
            for (const char* field : {"releaseDate", "composerName", "genreNames", "isrc",
                                      "contentRating", "recordLabel", "upc", "copyright",
                                      "isCompilation", "isComplete", "hasLyrics", "artwork",
                                      "workName", "movementName", "movementNumber",
                                      "movementCount", "attribution"}) {
                const cJSON* value = cJSON_GetObjectItemCaseSensitive(attrs, field);
                if (value) cJSON_AddItemToObject(hit, field, cJSON_Duplicate(value, true));
            }
            if (type == "albums") {
                const cJSON* notes = cJSON_GetObjectItemCaseSensitive(attrs, "editorialNotes");
                if (cJSON_IsObject(notes)) cJSON_AddItemToObject(hit, "editorialNotes", cJSON_Duplicate(notes, true));
            }
        }
        if (metadata) {
            const cJSON* relationships = cJSON_GetObjectItemCaseSensitive(item, "relationships");
            const std::initializer_list<const char*> videoRelations = {"albums", "artists", "genres", "songs"};
            const std::initializer_list<const char*> otherRelations = {"albums", "artists", "composers", "genres"};
            for (const char* relation : musicVideo ? videoRelations : otherRelations) {
                const cJSON* group = cJSON_GetObjectItemCaseSensitive(relationships, relation);
                const cJSON* entries = cJSON_GetObjectItemCaseSensitive(group, "data");
                if (!cJSON_IsArray(entries) || cJSON_GetObjectItemCaseSensitive(group, "next")) continue;
                cJSON* names = cJSON_AddArrayToObject(hit, relation);
                const cJSON* member = nullptr;
                cJSON_ArrayForEach(member, entries) {
                    const cJSON* memberId = cJSON_GetObjectItemCaseSensitive(member, "id");
                    const cJSON* memberAttrs = cJSON_GetObjectItemCaseSensitive(member, "attributes");
                    const cJSON* memberName = cJSON_GetObjectItemCaseSensitive(memberAttrs, "name");
                    cJSON* entry = cJSON_CreateObject();
                    cJSON_AddItemToArray(names, entry);
                    if (cJSON_IsString(memberId)) cJSON_AddStringToObject(entry, "id", memberId->valuestring);
                    if (cJSON_IsString(memberName)) cJSON_AddStringToObject(entry, "name", memberName->valuestring);
                }
            }
            const cJSON* credits = cJSON_GetObjectItemCaseSensitive(relationships, "credits");
            const cJSON* groups = cJSON_GetObjectItemCaseSensitive(credits, "data");
            if (cJSON_IsArray(groups)) cJSON_AddItemToObject(hit, "credits", cJSON_Duplicate(groups, true));
            const cJSON* href = cJSON_GetObjectItemCaseSensitive(item, "href");
            if (cJSON_IsString(href)) cJSON_AddStringToObject(hit, "href", href->valuestring);
        }
    }
    if (collection && upstreamNext) {
        // 客户端只从分页地址读偏移量，请求仍发往固定目录端点。
        cJSON_AddStringToObject(data, "next", upstreamNext->valuestring);
    }
    cJSON_Delete(root);
    res.set_content(json_success(data), "application/json");
}

static void handle_m3u8(const httplib::Request& req, httplib::Response& res) {
    auto adamId = req.get_param_value("adamId");
    if (adamId.empty()) {
        res.set_content(json_error(400, "missing adamId"), "application/json");
        return;
    }

    std::string m3u8 = get_m3u8(adamId);
    if (m3u8.empty()) {
        res.set_content(json_error(404, "failed to get m3u8"), "application/json");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    cJSON_AddStringToObject(data, "adamId", adamId.c_str());
    cJSON_AddStringToObject(data, "m3u8", m3u8.c_str());
    res.set_content(json_success(data), "application/json");
}

static void handle_key(const httplib::Request& req, httplib::Response& res) {
    auto adamId = req.get_param_value("adamId");
    auto uri = req.get_param_value("uri");
    if (adamId.empty()) {
        res.set_content(json_error(400, "missing adamId"), "application/json");
        return;
    }
    if (uri.empty()) {
        res.set_content(json_error(400, "missing uri"), "application/json");
        return;
    }
    /* The prefetch key URI (adamId=0) derives a shared context template, not a
       playable song key.  Requesting it with a real adamId yields a key that
       cannot decrypt the track, so reject that combination. */
    static const char* kPrefetchUri = "skd://itunes.apple.com/P000000000/s1/e1";
    if (adamId != "0" && uri == kPrefetchUri) {
        res.set_content(json_error(400, "invalid uri for adamId"), "application/json");
        return;
    }

    uint8_t cap_ctx[0x8000], cap_state[0x2100];
    uint64_t rcx = 0, rax = 0, rdx = 0, r9 = 0, rbp = 0;
    std::string contentKey = get_key(adamId, uri, cap_ctx, cap_state,
                                              &rcx, &rax, &rdx, &r9, &rbp);
    if (contentKey.empty()) {
        res.set_content(json_error(500, "key retrieval failed"), "application/json");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    cJSON_AddStringToObject(data, "adamId", adamId.c_str());
    cJSON_AddStringToObject(data, "keyUri", uri.c_str());
    cJSON_AddStringToObject(data, "contentKey", contentKey.c_str());
    if (rcx || rax || rdx || r9 || rbp) {
        cJSON_AddStringToObject(data, "ctx", b64_encode(cap_ctx, 0x8000).c_str());
        cJSON_AddStringToObject(data, "state", b64_encode(cap_state, 0x2100).c_str());
        char tmp[64];
        snprintf(tmp, sizeof(tmp), "0x%llx", (unsigned long long)rcx);
        cJSON_AddStringToObject(data, "rcx", tmp);
        snprintf(tmp, sizeof(tmp), "0x%llx", (unsigned long long)rax);
        cJSON_AddStringToObject(data, "rax", tmp);
        snprintf(tmp, sizeof(tmp), "0x%llx", (unsigned long long)rdx);
        cJSON_AddStringToObject(data, "rdx", tmp);
        snprintf(tmp, sizeof(tmp), "0x%llx", (unsigned long long)r9);
        cJSON_AddStringToObject(data, "r9", tmp);
        snprintf(tmp, sizeof(tmp), "0x%llx", (unsigned long long)rbp);
        cJSON_AddStringToObject(data, "rbp", tmp);
    }
    res.set_content(json_success(data), "application/json");
}

static void handle_lyrics(const httplib::Request& req, httplib::Response& res) {
    auto adamId = req.get_param_value("adamId");
    auto language = req.get_param_value("language");
    auto syllable = req.get_param_value("syllable");
    auto script = req.get_param_value("script");
    if (adamId.empty()) {
        res.set_content(json_error(400, "missing adamId"), "application/json");
        return;
    }
    if (language.empty()) language = "en";
    /* syllable=0|false|no -> standard /lyrics; default (and syllable=1) ->
       word-timed /syllable-lyrics. */
    bool use_syllable = true;
    if (!syllable.empty()) {
        std::string s = syllable;
        std::transform(s.begin(), s.end(), s.begin(),
                       [](unsigned char c){ return (char)std::tolower(c); });
        if (s == "0" || s == "false" || s == "no" || s == "off") use_syllable = false;
    }

    WebTokens tokens = get_web_tokens();
    if (!tokens.valid()) {
        res.set_content(json_error(500, "missing music/dev token, run --login first"), "application/json");
        return;
    }

    std::string lyrics = AppleApi::getLyrics(adamId, tokens.storefront_id, language,
                                              use_syllable, script,
                                              tokens.dev_token, tokens.music_token);
    if (lyrics.empty()) {
        res.set_content(json_error(404, "lyrics not found"), "application/json");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    cJSON_AddStringToObject(data, "adamId", adamId.c_str());
    cJSON_AddStringToObject(data, "syllable", use_syllable ? "true" : "false");
    cJSON_AddStringToObject(data, "lyrics", lyrics.c_str());
    res.set_content(json_success(data), "application/json");
}

static void handle_webplayback(const httplib::Request& req, httplib::Response& res) {
    auto adamId = req.get_param_value("adamId");
    if (adamId.empty()) {
        res.set_content(json_error(400, "missing adamId"), "application/json");
        return;
    }

    WebTokens tokens = get_web_tokens();
    if (!tokens.valid()) {
        res.set_content(json_error(500, "missing music/dev token, run --login first"), "application/json");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    std::string m3u8 = AppleApi::getWebPlayback(adamId, tokens.dev_token, tokens.music_token, data);
    if (m3u8.empty()) {
        cJSON_Delete(data);
        res.set_content(json_error(404, "webplayback not available"), "application/json");
        return;
    }

    cJSON_AddStringToObject(data, "adamId", adamId.c_str());
    cJSON_AddStringToObject(data, "m3u8", m3u8.c_str());
    res.set_content(json_success(data), "application/json");
}

static void handle_license(const httplib::Request& req, httplib::Response& res) {
    cJSON* req_json = cJSON_Parse(req.body.c_str());
    if (!req_json) {
        res.set_content(json_error(400, "invalid JSON body"), "application/json");
        return;
    }

    const char* adamId_s = cJSON_GetStringValue(cJSON_GetObjectItemCaseSensitive(req_json, "adamId"));
    const char* challenge_s = cJSON_GetStringValue(cJSON_GetObjectItemCaseSensitive(req_json, "challenge"));
    const char* uri_s = cJSON_GetStringValue(cJSON_GetObjectItemCaseSensitive(req_json, "uri"));
    const char* drmType_s = cJSON_GetStringValue(cJSON_GetObjectItemCaseSensitive(req_json, "drm-type"));
    std::string adamId = adamId_s ? adamId_s : "";
    std::string challenge = challenge_s ? challenge_s : "";
    std::string uri = uri_s ? uri_s : "";
    std::string drmType = drmType_s ? drmType_s : "";
    cJSON_Delete(req_json);

    if (adamId.empty() || challenge.empty() || uri.empty()) {
        res.set_content(json_error(400, "missing adamId, challenge, or uri"), "application/json");
        return;
    }

    if (drmType.empty()) drmType = "wv";
    if (drmType != "wv" && drmType != "pr") {
        res.set_content(json_error(400, "drm-type must be wv or pr"), "application/json");
        return;
    }

    WebTokens tokens = get_web_tokens();
    if (!tokens.valid()) {
        res.set_content(json_error(500, "missing music/dev token, run --login first"), "application/json");
        return;
    }

    std::string license;
    int renew = 0;
    if (!AppleApi::getLicense(adamId, challenge, uri, tokens.dev_token, tokens.music_token, drmType, license, renew)) {
        res.set_content(json_error(500, "license acquisition failed"), "application/json");
        return;
    }

    cJSON* data = cJSON_CreateObject();
    cJSON_AddStringToObject(data, "adamId", adamId.c_str());
    cJSON_AddStringToObject(data, "license", license.c_str());
    cJSON_AddNumberToObject(data, "renew", renew);
    res.set_content(json_success(data), "application/json");
}


/* ============================== */
/*     Background tasks           */
/* ============================== */

static void token_refresh_worker() {
    while (!g_refresh_stop.load()) {
        for (int i = 0; i < g_token_refresh_interval && !g_refresh_stop.load(); ++i) {
            std::this_thread::sleep_for(std::chrono::seconds(1));
        }
        if (g_refresh_stop.load()) break;

        LOG_INFO("background token refresh starting");
        std::string sf, dev, music;
        if (refresh_tokens(sf, dev, music)) {
            std::lock_guard<std::mutex> lock(g_tokens_mutex);
            if (!sf.empty()) {
                g_tokens.storefront_id = normalize_storefront_id(sf);
            }
            if (!dev.empty()) g_tokens.dev_token = dev;
            if (!music.empty()) g_tokens.music_token = music;
            save_token_cache();
            LOG_INFO("background token refresh completed");
        } else {
            LOG_WARN("background token refresh failed");
        }
    }
}

static void signal_worker() {
    while (!g_refresh_stop.load()) {
        int sig = 0;
        if (sigwait(&g_signal_set, &sig) == 0) {
            if (sig == SIGINT || sig == SIGTERM) {
                LOG_INFO("received signal %d, stopping service", sig);
                g_refresh_stop.store(true);
                if (g_svr) g_svr->stop();
                break;
            }
        }
    }
}

/* ============================== */
/*     Main entry point           */
/* ============================== */

static void print_usage() {
    LOG_INFO("usage: lite [--login user:pass] [--host 127.0.0.1] [--port 12340]");
    LOG_INFO("            [--device-info STR] [--base-dir data] [--proxy URL] [--debug]");
    LOG_INFO("            [--log-level debug|info|warn|error] [--log-file PATH]");
    LOG_INFO("            [--token-refresh-interval SECONDS] [--cors]");
    LOG_INFO("            [--dns ip[,ip...]] [--ca-bundle PATH]");
    LOG_INFO("            [--tls auto|1.3|default]");
}

static LogLevel parse_log_level(const std::string& s) {
    if (s == "debug") return LogLevel::Debug;
    if (s == "warn") return LogLevel::Warn;
    if (s == "error") return LogLevel::Error;
    return LogLevel::Info;
}

int main(int argc, char* argv[]) {
    setenv("ANDROID_DATA", "/data", 1);
    setenv("ANDROID_ROOT", "/system", 1);
    setenv("TZ", "UTC", 1);

    std::vector<std::string> cmdline_args;
    cmdline_args.push_back(argv[0]);
    const char* args_file = getenv("LITE_ARGS_FILE");
    if (args_file && *args_file) {
        std::ifstream af(args_file);
        std::string line;
        while (std::getline(af, line)) {
            if (!line.empty() && (line.back() == '\r')) line.pop_back();
                        line.erase(std::remove_if(line.begin(), line.end(), [](char c){ return c == 0; }), line.end());
            if (line.empty()) continue;
            size_t b = line.find_first_not_of(" 	");
            if (b == std::string::npos) continue;
            size_t e = line.find_last_not_of(" 	");
            line = line.substr(b, e - b + 1);
            if (!line.empty()) cmdline_args.push_back(line);
        }
    } else {
        for (int i = 1; i < argc; i++) cmdline_args.push_back(argv[i]);
    }
    for (size_t i = 1; i < cmdline_args.size(); i++) {
        std::string arg = cmdline_args[i];
        if (arg == "--host" && i + 1 < cmdline_args.size()) g_host = cmdline_args[++i];
        else if (arg == "--port" && i + 1 < cmdline_args.size()) g_port = atoi(cmdline_args[++i].c_str());
        else if (arg == "--debug") { g_log_level = "debug"; g_ssl_verify_disabled = true; }
        else if (arg == "--code-from-file") g_code_from_file = true;
        else if (arg == "--log-level" && i + 1 < cmdline_args.size()) g_log_level = cmdline_args[++i];
        else if (arg == "--log-file" && i + 1 < cmdline_args.size()) g_log_file = cmdline_args[++i];
        else if (arg == "--token-refresh-interval" && i + 1 < cmdline_args.size()) g_token_refresh_interval = atoi(cmdline_args[++i].c_str());
        else if (arg == "--cors") g_cors_enabled = true;
        else if (arg == "--proxy" && i + 1 < cmdline_args.size()) {
            g_proxy = cmdline_args[++i];
            setenv("all_proxy", g_proxy.c_str(), 1);
        }
        else if (arg == "--login" && i + 1 < cmdline_args.size()) {
            g_login_only = true;
            g_login_credentials = cmdline_args[++i];
        }
        else if (arg == "--device-info" && i + 1 < cmdline_args.size()) g_device_info_override = cmdline_args[++i];
        else if (arg == "--base-dir" && i + 1 < cmdline_args.size()) g_base_dir = cmdline_args[++i];
        else if (arg == "--dns" && i + 1 < cmdline_args.size()) g_dns_servers = cmdline_args[++i];
        else if (arg == "--ca-bundle" && i + 1 < cmdline_args.size()) g_ca_bundle = cmdline_args[++i];
        else if (arg == "--tls" && i + 1 < cmdline_args.size()) {
            const std::string v = cmdline_args[++i];
            if (v == "auto") g_tls_mode = TLS_MODE_AUTO;
            else if (v == "1.3" || v == "13" || v == "tls1.3") g_tls_mode = TLS_MODE_13;
            else if (v == "default" || v == "off") g_tls_mode = TLS_MODE_DEFAULT;
            else {
                LOG_ERROR("invalid --tls value: %s (use auto, 1.3 or default)", v.c_str());
                return 1;
            }
        }
        else if (arg == "--help" || arg == "-h") {
            print_usage();
            return 0;
        }
        else {
            LOG_ERROR("unknown argument: %s", arg.c_str());
            print_usage();
            return 1;
        }
    }

    /* Environment fallbacks: command-line flags take precedence. */
    if (g_dns_servers.empty()) {
        const char* v = getenv("LITE_DNS");
        if (v && *v) g_dns_servers = v;
    }
    if (g_ca_bundle.empty()) {
        const char* v = getenv("LITE_CA_BUNDLE");
        if (v && *v) g_ca_bundle = v;
    }

    if (g_token_refresh_interval <= 0) g_token_refresh_interval = 1800;
    Logger::get().configure(parse_log_level(g_log_level), g_log_file, 5 * 1024 * 1024);
    set_base_dir(g_base_dir.c_str());
    if (!g_dns_servers.empty()) set_dns_servers(g_dns_servers.c_str());
    if (!g_ca_bundle.empty()) set_ca_bundle(g_ca_bundle.c_str());
    if (!g_ssl_verify_disabled) {
        FILE* ca = fopen(get_ca_bundle(), "r");
        if (ca) fclose(ca);
        else LOG_ERROR("TLS verification is enabled but the CA bundle %s is not readable;"
                       " pass --ca-bundle <path> or run with --debug", get_ca_bundle());
    }
    g_tokens.base_dir = g_base_dir;
    LOG_INFO("tls: %s",
             g_tls_mode == TLS_MODE_13      ? "TLS 1.3 only"
           : g_tls_mode == TLS_MODE_DEFAULT ? "library default"
                                            : "TLS 1.3 preferred, default fallback");

    if (g_login_only) {
        auto colon = g_login_credentials.find(':');
        if (colon == std::string::npos) {
            LOG_ERROR("invalid login format, expected user:pass");
            return 1;
        }
        std::string username = g_login_credentials.substr(0, colon);
        std::string password = g_login_credentials.substr(colon + 1);
        set_credentials(username.c_str(), password.c_str());
        g_resolved_device_info = resolve_device_info(username);

        LOG_INFO("wrapper-lite login mode");

        /* Run the whole login + native token refresh in a child process.
         * On Termux + QEMU TCG the Android URLRequest destructors corrupt the
         * heap; isolating login in a child keeps this process's heap intact. */
        pid_t pid = fork();
        if (pid < 0) {
            LOG_ERROR("fork failed");
            return 1;
        }
        if (pid == 0) {
            install_hooks();
            set_device_info(g_resolved_device_info.c_str());
            g_reqCtx = init_ctx();
            if (!login(g_reqCtx)) {
                LOG_ERROR("login failed");
                _exit(1);
            }
            LOG_INFO("login successful");
            if (!cache_login_tokens()) {
                LOG_ERROR("failed to cache account info");
                _exit(1);
            }
            _exit(0);
        }

        int status = 0;
        waitpid(pid, &status, 0);

        /* Read token files (written by the child) into this clean process. */
        auto readFile = [](const std::string& path) {
            std::ifstream f(path);
            if (!f) return std::string();
            std::string c((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
            while (!c.empty() && (c.back() == ' ' || c.back() == 10 || c.back() == 13)) c.pop_back();
            return c;
        };
        g_tokens.base_dir = g_base_dir;
        g_tokens.storefront_id = normalize_storefront_id(readFile(std::string(g_base_dir) + "/STOREFRONT_ID"));
        g_tokens.dev_token = readFile(std::string(g_base_dir) + "/DEV_TOKEN");
        g_tokens.music_token = readFile(std::string(g_base_dir) + "/MUSIC_TOKEN");
        if (g_tokens.dev_token.empty() || g_tokens.music_token.empty()) {
            LOG_ERROR("failed to cache account info");
            return 1;
        }
        {
            std::lock_guard<std::mutex> lock(g_tokens_mutex);
            save_token_cache();
        }
        LOG_INFO("login complete, exiting");
        return 0;
    }


    /* Service mode */
    /* Block termination signals before Android/Apple libraries spawn their
       internal threads; new threads inherit this mask.  Our signal_worker
       consumes SIGINT/SIGTERM via sigwait and stops the HTTP server. */
    sigemptyset(&g_signal_set);
    sigaddset(&g_signal_set, SIGINT);
    sigaddset(&g_signal_set, SIGTERM);
    pthread_sigmask(SIG_BLOCK, &g_signal_set, nullptr);

    install_hooks();
    g_resolved_device_info = resolve_device_info(""); /* no username in service mode */
    set_device_info(g_resolved_device_info.c_str());
    g_reqCtx = init_ctx();
    setup_services();
    load_token_cache();
    WebTokens initial_tokens = get_web_tokens();
    if (!initial_tokens.valid()) {
        LOG_WARN("missing music/dev token, run --login first");
    }

    httplib::Server svr;

    svr.set_read_timeout(10, 0);
    svr.set_write_timeout(30, 0);
    svr.set_keep_alive_max_count(256);
    svr.set_keep_alive_timeout(30);
    svr.set_payload_max_length(1 << 20);
    svr.set_tcp_nodelay(true);

    /* CORS (opt-in via --cors; the API has no authentication): default
       headers are copied into every response (handlers, error handler and
       httplib's own 4xx/5xx), so browsers can call the API from any origin.
       OPTIONS preflights (e.g. POST /license with a JSON body) are answered
       with 204, including Chromium's Private Network Access opt-in so public
       pages may reach a loopback/LAN instance. */
    if (g_cors_enabled) {
        svr.set_default_headers({
            {"Access-Control-Allow-Origin", "*"},
            {"Access-Control-Allow-Methods", "GET, POST, OPTIONS"},
            {"Access-Control-Allow-Headers", "*"},
            {"Access-Control-Max-Age", "86400"},
        });
        svr.Options(".*", [](const httplib::Request&, httplib::Response& res) {
            res.set_header("Access-Control-Allow-Private-Network", "true");
            res.status = 204;
        });
    }

    svr.set_pre_routing_handler([](const httplib::Request& req, httplib::Response& res) {
        (void)res;
        LOG_INFO("request: %s %s", req.method.c_str(), req.target.c_str());
        return httplib::Server::HandlerResponse::Unhandled;
    });

    svr.Get("/catalog/search", handle_catalog_search);
    svr.Get("/catalog/item", [](const httplib::Request& req, httplib::Response& res) {
        handle_catalog_detail(req, res, CatalogLookup::Item);
    });
    svr.Get("/catalog/tracks", [](const httplib::Request& req, httplib::Response& res) {
        handle_catalog_detail(req, res, CatalogLookup::AlbumTracks);
    });
    svr.Get("/catalog/music-videos", [](const httplib::Request& req, httplib::Response& res) {
        handle_catalog_detail(req, res, CatalogLookup::SongMusicVideos);
    });
    svr.Get("/m3u8", handle_m3u8);
    svr.Get("/key", handle_key);
    svr.Get("/lyrics", handle_lyrics);
    svr.Get("/webplayback", handle_webplayback);
    svr.Post("/license", handle_license);

    svr.Get("/status", [](const httplib::Request&, httplib::Response& res) {
        std::string storefront;
        {
            std::lock_guard<std::mutex> lock(g_tokens_mutex);
            storefront = g_tokens.storefront_id;
        }
        cJSON* data = cJSON_CreateObject();
        /* Regions this wrapper can serve.  Single-account for now, but the
           array shape mirrors wrapper-manager's StatusData.regions and
           prepares for future multi-wrapper aggregation. */
        cJSON* regions = cJSON_CreateArray();
        if (!storefront.empty()) {
            cJSON_AddItemToArray(regions, cJSON_CreateString(storefront.c_str()));
        }
        cJSON_AddItemToObject(data, "regions", regions);
        res.set_content(json_success(data), "application/json");
    });

    svr.set_error_handler([](const httplib::Request& req, httplib::Response& res) {
        // 保留目录详情接口区分资源不存在和路由不存在的错误正文。
        const bool catalogNotFound = (req.path == "/catalog/item" || req.path == "/catalog/tracks" ||
                                      req.path == "/catalog/music-videos") && !res.body.empty();
        if (res.status == 404 && !catalogNotFound)
            res.set_content(json_error(404, "not found"), "application/json");
    });
    svr.set_exception_handler([](const httplib::Request&, httplib::Response& res, std::exception_ptr ep) {
        try {
            if (ep) std::rethrow_exception(ep);
        } catch (const std::exception& e) {
            LOG_ERROR("handler exception: %s", e.what());
        } catch (...) {
            LOG_ERROR("handler exception: unknown");
        }
        res.set_content(json_error(500, "internal error"), "application/json");
    });

    g_refresh_stop.store(false);
    std::thread refresh_thread(token_refresh_worker);
    std::thread sig_thread(signal_worker);
    g_svr = &svr;

    LOG_INFO("wrapper-lite listening on %s:%d", g_host.c_str(), g_port);
    svr.listen(g_host.c_str(), g_port);

    g_refresh_stop.store(true);
    pthread_kill(sig_thread.native_handle(), SIGTERM);
    if (refresh_thread.joinable()) refresh_thread.join();
    if (sig_thread.joinable()) sig_thread.join();
    {
        std::lock_guard<std::mutex> lock(g_tokens_mutex);
        save_token_cache();
    }
    g_svr = nullptr;
    LOG_INFO("wrapper-lite stopped");

    return 0;
}
