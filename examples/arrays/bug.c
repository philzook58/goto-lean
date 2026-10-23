#include <assert.h>
#include ".lake/lower_bound_bug.c"
int main(void) {
    int a[3] = {1, 1, 1};
    unsigned result = lower_bound_bug(a, 3, 1);
    assert(result == 0);
}
