#include <assert.h>
#include "algorithms.c"
#ifndef N
#define N 4
#endif
#ifndef CASE
#define CASE 1
#endif
extern unsigned nondet_size(void);
extern int nondet_int(void);

int main(void) {
    int a[N], before[N], key = nondet_int();
    unsigned n = nondet_size();
    __CPROVER_assume(n <= N);
    for (unsigned i = 0; i < N; ++i) a[i] = before[i] = nondet_int();
#if CASE == 1
    fill(a, n, key);
    for (unsigned i = 0; i < n; ++i) assert(a[i] == key);
#elif CASE == 2
    unsigned r = find(a, n, key);
    assert(r <= n);
    for (unsigned i = 0; i < r; ++i) assert(a[i] != key);
    if (r < n) assert(a[r] == key);
#elif CASE == 3
    unsigned r = is_sorted_until(a, n);
    assert(r <= n);
    for (unsigned i = 1; i < r; ++i) assert(a[i-1] <= a[i]);
    if (r < n) { assert(r > 0); assert(a[r-1] > a[r]); }
#elif CASE == 4
    unsigned pivot = nondet_size();
    __CPROVER_assume(pivot <= n);
    unsigned r = rotate(a, pivot, n);
    assert(r == n-pivot);
    for (unsigned i = 0; i < n; ++i) assert(a[i] == before[(i+pivot)%n]);
#elif CASE == 5
    bubble_sort(a, n);
    for (unsigned i = 1; i < n; ++i) assert(a[i-1] <= a[i]);
    /* Count every original value to check permutation, including duplicates. */
    for (unsigned i = 0; i < n; ++i) {
        unsigned old_count = 0, new_count = 0;
        for (unsigned j = 0; j < n; ++j) {
            old_count += before[j] == before[i];
            new_count += a[j] == before[i];
        }
        assert(old_count == new_count);
    }
#elif CASE == 6
    for (unsigned i = 1; i < n; ++i) __CPROVER_assume(a[i-1] <= a[i]);
    unsigned r = lower_bound(a, n, key);
    assert(r <= n);
    for (unsigned i = 0; i < r; ++i) assert(a[i] < key);
    for (unsigned i = r; i < n; ++i) assert(a[i] >= key);
#elif CASE == 7
    reverse(a, n);
    for (unsigned i = 0; i < n; ++i) assert(a[i] == before[n-1-i]);
#endif
    for (unsigned i = n; i < N; ++i) assert(a[i] == before[i]);
#if CASE == 2 || CASE == 3 || CASE == 6
    for (unsigned i = 0; i < n; ++i) assert(a[i] == before[i]);
#endif
}
