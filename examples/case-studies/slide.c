#define _XOPEN_SOURCE 500
#include "checks.h"
#define main original_2048_main
#include "upstream/2048/2048.c"
#undef main

/* Four exponent bytes: 0 = empty, n > 0 = tile 2^n. The score starts at zero. */
uint64_t slide_case(uint32_t input) {
    uint8_t row[4];
    for (unsigned i = 0; i < 4; ++i) row[i] = input >> (8*i);
    score = 0;
    bool moved = slideArray(row);
    uint32_t output = 0;
    for (unsigned i = 0; i < 4; ++i) output |= (uint32_t)row[i] << (8*i);
    CHECK(moved == (input != output), "move flag agrees with changed row");
    return ((uint64_t)score << 32) | output;
}

void slide_small(unsigned input) {
    REQUIRE((input & 255) <= 4 && ((input >> 8) & 255) <= 4 &&
            ((input >> 16) & 255) <= 4 && (input >> 24) <= 4);
    uint64_t out = slide_case(input);
    unsigned before = 0, after = 0;
    for (unsigned i = 0; i < 4; ++i) {
        unsigned a = (input >> (8*i)) & 255, b = (out >> (8*i)) & 255;
        if (a) before += 1u << a;
        if (b) after += 1u << b;
    }
    CHECK(before == after, "sliding preserves tile mass");
}

/* A merge increments exponent 31 to 32, making the upstream score shift undefined. */
void slide_large(void) { (void)slide_case(0x00001f1fu); }

void slide_no_double_merge(void) {
    uint64_t out = slide_case(0x00020101u); /* [2,2,4,empty] as tile values */
    CHECK(out == (UINT64_C(4) << 32 | 0x00000202u), "a tile merges at most once per move");
}
