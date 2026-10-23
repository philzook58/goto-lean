#include <stdint.h>

uint32_t increment(uint32_t x) { return x + 1; }
uint32_t maximum(uint32_t x, uint32_t y) { return x < y ? y : x; }
uint32_t countdown(uint32_t n) {
  while (n != 0) --n;
  return n;
}
extern uint32_t nondet_uint(void);
uint32_t constrained(void) {
  uint32_t x = nondet_uint();
  __CPROVER_assume(x < 10);
  __CPROVER_assert(x <= 9, "bounded choice");
  return x;
}
uint32_t bad(uint32_t x) {
  __CPROVER_assert(x != 7, "seven is forbidden");
  return x;
}
