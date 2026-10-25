#include <inttypes.h>
#include <stdio.h>
#include "checks.h"

_Static_assert(sizeof(int) == 4 && sizeof(JsonReport) == 80, "JSON report needs the 32-bit-int ABI");

int main(void) {
    char kind[16];
    uint64_t a;
    unsigned b, c;
    while (scanf("%15s %" SCNu64 " %u %u", kind, &a, &b, &c) == 4) {
        if (kind[0] == 'j') {
            JsonReport r = json_case(a, b, c);
            printf("%u %u %u %u", (unsigned)r.result, r.pos, r.next, (unsigned)r.parent);
            for (unsigned i = 0; i < 16; ++i) printf(" %u", (unsigned)r.tokens[i]);
        } else if (kind[0] == 's') printf("%" PRIu64, slide_case(a));
        else printf("%u", lookup_case(a));
        putchar('\n');
    }
    return 0;
}
