/* Scalar adaptations of:
 * Kroening, Schrammel, Tautschnig, arXiv:2302.02384v1, Sections 2, 3.1, 3.3 (CC BY 4.0).
 * Philip Zucker, https://www.philipzucker.com/cbmc_tut/ (2024-01-29).
 * Nondeterministic harness inputs are parameters except the explicit uninitialized example.
 * lock/unlock are source-inlined and the global LOCK is a local held flag.
 */
#include <stdint.h>

int uninitialized(void) {
  int x;
  __CPROVER_assert(x != 12345, "uninitialized != 12345");
  return 0;
}
int guarded(int x) {
  if (x <= 42) __CPROVER_assert(x != 12345, "guarded != 12345");
  return 0;
}
int64_t abs64(int64_t x) {
  int64_t y = x <= 0 ? -x : x;
  __CPROVER_assert(y >= 0, "absolute value nonnegative");
  return y;
}
int abs32(int x) {
  int y = x;
  if (x < 0) y = -x;
  __CPROVER_assert(y >= 0, "absolute value nonnegative");
  return y;
}
unsigned before_assume(unsigned result) {
  __CPROVER_assert(result < 100, "range < 100 before assume");
  __CPROVER_assume(result >= 1 && result <= 100);
  return result;
}
unsigned after_assume(unsigned result) {
  __CPROVER_assume(result >= 1 && result <= 100);
  __CPROVER_assert(result < 100, "range < 100 after assume");
  return result;
}
unsigned range_fixed(unsigned result) {
  __CPROVER_assume(result >= 1 && result <= 100);
  __CPROVER_assert(result <= 100, "range <= 100 after assume");
  return result;
}

_Bool nondet_bool(void);
unsigned lock_bug(unsigned times) {
#ifdef LOCK_BOUND
  __CPROVER_assume(times <= LOCK_BOUND);
#endif
  unsigned got_lock = 0, held = 0;
  while (times > 0) {
    if (nondet_bool()) {
      __CPROVER_assert(!held, "acquire unlocked");
      held = 1;
      got_lock++;
    }
    if (got_lock != 0) {
      __CPROVER_assert(held, "release locked");
      held = 0;
    }
    got_lock--; /* Paper bug: decrements even when acquisition failed. */
    times--;
  }
  return got_lock;
}
unsigned lock_fixed(unsigned times) {
#ifdef LOCK_BOUND
  __CPROVER_assume(times <= LOCK_BOUND);
#endif
  unsigned got_lock = 0, held = 0;
  while (times > 0) {
    if (nondet_bool()) {
      __CPROVER_assert(!held, "acquire unlocked");
      held = 1;
      got_lock++;
    }
    if (got_lock != 0) {
      __CPROVER_assert(held, "release locked");
      held = 0;
      got_lock--; /* Repair: decrement only when a lock was held. */
    }
    times--;
  }
  return got_lock;
}
