#include <limits.h>

/* The excluded input is visible here: signed abs cannot represent abs(INT_MIN). */
int checked_abs(int x) {
  __CPROVER_assume(x != INT_MIN);
  int result = x < 0 ? -x : x;
  __CPROVER_assert(result >= 0, "absolute value is nonnegative");
  return result;
}

/* The assumption is the caller's obligation; the assertion is our guarantee. */
int checked_index(unsigned i) {
  int primes[4] = {2, 3, 5, 7};
  __CPROVER_assume(i < 4);
  int result = primes[i];
  __CPROVER_assert(result > 0, "selected prime is positive");
  return result;
}

int checked_divide(int x, int divisor) {
  __CPROVER_assume(divisor != 0);
  __CPROVER_assume(!(x == INT_MIN && divisor == -1));
  int result = x / divisor;
  __CPROVER_assert(divisor != 1 || result == x, "division by one is identity");
  return result;
}

unsigned checked_shift(unsigned x, unsigned distance) {
  __CPROVER_assume(distance < 32);
  unsigned result = x << distance;
  __CPROVER_assert(distance != 0 || result == x, "shift by zero is identity");
  return result;
}

int checked_add(int x) {
  __CPROVER_assume(x < INT_MAX);
  int result = x + 1;
  __CPROVER_assert(result > x, "increment increases the value");
  return result;
}
