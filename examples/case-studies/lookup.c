#include "checks.h"
#include "upstream/khash/khash.h"
KHASH_MAP_INIT_INT(study, unsigned)

/* A valid four-bucket collision chain: key 0 was deleted; keys 4 and 8 remain. */
unsigned lookup_case(unsigned key) {
    khint8_t flags[4] = {1, 0, 2, 0};
    khint32_t keys[4] = {0, 4, 0, 8};
    unsigned values[4] = {0, 40, 0, 80};
    khash_t(study) table = {4, 2, 3, 3, flags, keys, values};
    unsigned found = kh_get(study, &table, key);
    unsigned expected = key == 4 ? 1 : key == 8 ? 3 : 4;
    CHECK(found == expected, "lookup crosses tombstones and preserves collision chain");
    return found;
}

void lookup_deleted_claim(void) {
    CHECK(lookup_case(0) == 0, "deleted key is still present");
}
