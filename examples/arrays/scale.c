#include <stdio.h>
#include <string.h>
#include "algorithms.c"

/* One request per line: operation, length, argument, then the array elements. */
int main(void) {
    char op[16];
    unsigned n, result;
    int argument, storage[258];
    while (scanf("%15s%u%d", op, &n, &argument) == 3) {
        if (n > 256) return 2;
        int *a = storage + 1;
        storage[0] = 12345678;
        a[n] = -12345678;
        for (unsigned i = 0; i < n; ++i)
            if (scanf("%d", &a[i]) != 1) return 2;
        result = 0;
        if (!strcmp(op, "fill")) fill(a, n, argument);
        else if (!strcmp(op, "find")) result = find(a, n, argument);
        else if (!strcmp(op, "prefix")) result = is_sorted_until(a, n);
        else if (!strcmp(op, "rotate")) {
            if (argument < 0 || (unsigned)argument > n) return 2;
            result = rotate(a, (unsigned)argument, n);
        }
        else if (!strcmp(op, "sort")) bubble_sort(a, n);
        else return 2;
        if (storage[0] != 12345678 || a[n] != -12345678) return 3;
        printf("%u", result);
        for (unsigned i = 0; i < n; ++i) printf(" %d", a[i]);
        puts("");
    }
}
