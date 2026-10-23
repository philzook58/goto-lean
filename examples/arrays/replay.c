#include <stdio.h>
#include "algorithms.c"

/* Input: n, key, then n sorted ints. Output: index, then the reversed array. */
int main(void) {
    unsigned n;
    int key, a[256];
    while (scanf("%u%d", &n, &key) == 2) {
        if (n > 256) return 2;
        for (unsigned i = 0; i < n; ++i)
            if (scanf("%d", &a[i]) != 1) return 2;
        printf("%u", lower_bound(a, n, key));
        reverse(a, n);
        for (unsigned i = 0; i < n; ++i) printf(" %d", a[i]);
        puts("");
    }
}
