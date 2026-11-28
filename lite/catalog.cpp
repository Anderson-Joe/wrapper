#include "lite.h"

static std::string encode_query(const std::string& value) {
    const char* hex = "0123456789ABCDEF";
    std::string encoded;
    for (unsigned char ch : value) {
        if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
            (ch >= '0' && ch <= '9') || ch == '-' || ch == '_' || ch == '.' || ch == '~') {
            encoded += static_cast<char>(ch);
        } else {
            encoded += '%';
            encoded += hex[ch >> 4];
            encoded += hex[ch & 15];
        }
    }
    return encoded;
}

long AppleApi::searchCatalog(const std::string& region, const std::string& term,
                             const std::string& type, int limit, int offset,
                             const std::string& language,
                             const std::string& devToken, std::string& body) {
    std::string path = "/v1/catalog/" + region + "/search?term=" +
        encode_query(term) + "&types=" + type + "&limit=" + std::to_string(limit) +
        "&offset=" + std::to_string(offset);
    if (!language.empty()) path += "&l=" + encode_query(language);
    return getCatalogResponse(path, devToken, body);
}
