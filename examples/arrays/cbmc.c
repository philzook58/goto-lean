#include <assert.h>
#include "algorithms.c"
#ifndef N
#define N 8
#endif
extern unsigned nondet_size(void);
extern int nondet_int(void);

int main(void) {
    int a[N], before[N], key = nondet_int();
    unsigned n = nondet_size();
    __CPROVER_assume(n <= N);
    for (unsigned i = 0; i < N; ++i) a[i] = before[i] = nondet_int();
    for (unsigned i = 1; i < n; ++i) __CPROVER_assume(a[i-1] <= a[i]);
    unsigned result = lower_bound(a, n, key);
    assert(result <= n);
    for (unsigned i = 0; i < n; ++i) {
        assert(a[i] == before[i]);
        if (i < result) assert(a[i] < key);
        else assert(key <= a[i]);
    }
    reverse(a, n);
    for (unsigned i = 0; i < N; ++i) {
        if (i < n) assert(a[i] == before[n-1-i]);
        else assert(a[i] == before[i]);
    }
}
