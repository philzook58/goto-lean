/* A caller owns the array; it supplies no memory preconditions to Lean. */
#include "upstream/fill.h"

int fill_local(int value) {
    int a[4];
    fill(a, 4, value);
    __CPROVER_assert(a[0] == value && a[3] == value, "fill initialized both endpoints");
    return a[3];
}

/* Negative control: the last element stays zero when value is 1. */
int fill_local_bug(int value) {
    int a[4] = {0};
    fill(a, 3, value);
    __CPROVER_assert(a[0] == value && a[3] == value, "underfilled array");
    return a[3];
}
