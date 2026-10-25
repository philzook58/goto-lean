#include "checks.h"
#include "upstream/jsmn/jsmn.c"

/* Fresh parser, at most 8 input bytes and 4 output tokens; no parent links or strict mode. */
JsonReport json_case(uint64_t text, unsigned length, unsigned capacity) {
    REQUIRE(length <= 8 && capacity <= 4);
    char input[8];
    for (unsigned i = 0; i < 8; ++i) input[i] = (char)(text >> (8*i));
    jsmn_parser parser;
    jsmntok_t tokens[4] = {{0}};
    jsmn_init(&parser);
    int result = jsmn_parse(&parser, input, length, tokens, capacity);
    CHECK(parser.toknext <= capacity, "token allocation respects capacity");
    if (result >= 0) {
        CHECK((unsigned)result == parser.toknext, "reported count matches allocated tokens");
        for (unsigned i = 0; i < parser.toknext; ++i) {
            CHECK(0 <= tokens[i].start && tokens[i].start <= tokens[i].end,
                  "successful token has ordered offsets");
            CHECK((unsigned)tokens[i].end <= length, "successful token is inside input");
        }
    }
    JsonReport report = {result, parser.pos, parser.toknext, parser.toksuper, {0}};
    for (unsigned i = 0; i < 4; ++i) {
        report.tokens[4*i] = tokens[i].type;
        report.tokens[4*i+1] = tokens[i].start;
        report.tokens[4*i+2] = tokens[i].end;
        report.tokens[4*i+3] = tokens[i].size;
    }
    return report;
}

/* A deliberately wrong caller contract: tokenization is not full JSON validation. */
void json_validation_claim(void) {
    JsonReport r = json_case(UINT64_C(0x58757274), 4, 4); /* truX */
    CHECK(r.result < 0, "invalid JSON must be rejected");
}
