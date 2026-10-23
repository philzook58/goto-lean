#include <limits.h>

/* Wrong branch: a source-level functional assertion fails for x=0, y=1. */
unsigned bug_maximum(unsigned x, unsigned y) {
    unsigned r = x < y ? x : y;
    __CPROVER_assert(r >= x && r >= y, "maximum dominates both arguments");
    return r;
}
unsigned fixed_maximum(unsigned x, unsigned y) {
    unsigned r = x < y ? y : x;
    __CPROVER_assert(r >= x && r >= y, "maximum dominates both arguments");
    return r;
}

/* Widen before arithmetic, rather than casting an already-overflowed result. */
int bug_add(int x) { return x + 1; }
long long fixed_add(int x) { return (long long)x + 1; }
int bug_negate(int x) { return -x; }
long long fixed_negate(int x) { return -(long long)x; }

unsigned bug_divide_zero(unsigned x, unsigned divisor) { return x / divisor; }
unsigned fixed_divide_zero(unsigned x, unsigned divisor) {
    return divisor == 0 ? 0 : x / divisor;
}
int bug_divide_overflow(int x) { return x / -1; }
long long fixed_divide_overflow(int x) { return (long long)x / -1; }

unsigned bug_shift(unsigned x, unsigned distance) { return x << distance; }
unsigned fixed_shift(unsigned x, unsigned distance) {
    return distance < 32 ? x << distance : 0;
}

int bug_index(unsigned i) {
    int a[4] = {2, 3, 5, 7};
    return a[i];
}
int fixed_index(unsigned i) {
    int a[4] = {2, 3, 5, 7};
    return i < 4 ? a[i] : 0;
}

unsigned bug_null(void) {
    unsigned *p = 0;
    return *p;
}
unsigned fixed_null(void) {
    unsigned value = 7;
    unsigned *p = &value;
    return *p;
}

unsigned bug_one_past(void) {
    unsigned char a[2] = {1, 2};
    unsigned char *p = a + 2;
    return *p;
}
unsigned fixed_one_past(void) {
    unsigned char a[2] = {1, 2};
    unsigned char *p = a + 1;
    return *p;
}

unsigned bug_lifetime(void) {
    unsigned char *p;
    { unsigned char value = 4; p = &value; }
    return *p;
}
unsigned fixed_lifetime(void) {
    unsigned result;
    { unsigned char value = 4; unsigned char *p = &value; result = *p; }
    return result;
}

unsigned bug_uninitialized(void) {
    unsigned value;
    __CPROVER_assert(value == 0, "value was initialized to zero");
    return value;
}
unsigned fixed_uninitialized(void) {
    unsigned value = 0;
    __CPROVER_assert(value == 0, "value was initialized to zero");
    return value;
}

unsigned bug_loop_bound(void) {
    unsigned char a[4] = {0};
    for (unsigned i = 0; i <= 4; ++i) a[i] = 7;
    return a[3];
}
unsigned fixed_loop_bound(void) {
    unsigned char a[4] = {0};
    for (unsigned i = 0; i < 4; ++i) a[i] = 7;
    return a[3];
}
