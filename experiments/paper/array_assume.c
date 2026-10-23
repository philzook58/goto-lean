/* arXiv:2302.02384v1, Section 3.3; CC BY 4.0. Added the missing nondet_int declaration. */
#include <assert.h>
int nondet_int(void);
int main(void) {
  int a[10], x, y;
  x = nondet_int();
  y = nondet_int();
  __CPROVER_assume(x >= 0 && x < 10 && y >= 0 && y < 10);
  __CPROVER_assume(a[x] >= 0);
  assert(a[y] >= 0);
}
