/* arXiv:2302.02384v1, Section 3.1 lock.c; CC BY 4.0. Added assert.h. */
#include <assert.h>
_Bool nondet_bool(void);
unsigned int nondet_unsigned_int(void);
_Bool LOCK = 0;
_Bool lock(void) {
  if (nondet_bool()) {
    assert(!LOCK);
    LOCK = 1;
    return 1;
  }
  return 0;
}
void unlock(void) { assert(LOCK); LOCK = 0; }
int main(void) {
  unsigned got_lock = 0;
  unsigned times = nondet_unsigned_int();
  while (times > 0) {
    if (lock()) got_lock++;
    if (got_lock != 0) unlock();
    got_lock--;
    times--;
  }
}
