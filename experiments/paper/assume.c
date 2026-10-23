/* arXiv:2302.02384v1, Section 3.3; CC BY 4.0. BEFORE/AFTER select its three variants. */
#include <assert.h>
unsigned int nondet_uint(void);
unsigned int one_to_hundred(void) {
  unsigned int result = nondet_uint();
#ifdef BEFORE
  assert(result < 100);
#endif
  __CPROVER_assume(result >= 1 && result <= 100);
#ifdef AFTER
  assert(result < 100);
#endif
  return result;
}
