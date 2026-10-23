#include <stdint.h>
#include <stdbool.h>

uint32_t increment(uint32_t x) { return x + 1; }
uint32_t maximum(uint32_t x, uint32_t y) { return x < y ? y : x; }
uint32_t countdown(uint32_t n) { while (n != 0) --n; return n; }
uint8_t narrow(uint8_t x, uint8_t y) { return (uint8_t)(x + y); }
uint32_t mix(uint32_t x, uint32_t y) {
  return ((x ^ y) + (x & y)) ^ ((x | y) * 17u) ^ ~x;
}
uint32_t signed_cast(int8_t x) { return (uint32_t)(int32_t)x; }
uint32_t signed_compare(int32_t x, int32_t y) { return x < y ? 1u : 0u; }
uint32_t shift(uint32_t x, uint32_t y) { return (x << y) ^ (x >> y); }
int32_t arithmetic_shift(int32_t x, uint32_t y) { return x >> y; }
int32_t quotient(int32_t x, int32_t y) { return x / y; }
int32_t remainder(int32_t x, int32_t y) { return x % y; }
uint32_t unsigned_quotient(uint32_t x, uint32_t y) { return x / y; }
uint32_t unsigned_remainder(uint32_t x, uint32_t y) { return x % y; }
uint64_t wide(uint64_t x, uint64_t y) { return (x * y) ^ (x + y); }
uint32_t array_read(uint32_t i) {
  uint8_t a[4] = {7, 11, 19, 23};
  return a[i % 4];
}
uint32_t string_local(uint32_t i) {
  char text[5] = "abc";
  return (unsigned char)text[i % 5];
}
uint32_t array_write(uint32_t i, uint32_t x) {
  uint8_t a[4] = {1, 2, 3, 4};
  a[i % 4] = (uint8_t)x;
  return a[0] + 10u * a[1] + 100u * a[2] + 1000u * a[3];
}
uint32_t record_update(uint32_t x, uint32_t y) {
  struct record { uint8_t tag; uint32_t value; } r;
  r.tag = (uint8_t)x; r.value = y;
  r.tag += 3;
  return r.tag ^ r.value;
}
uint32_t nested_update(uint32_t i, uint32_t x) {
  struct record { uint16_t values[3]; uint8_t tag; } r;
  r.values[0] = 1; r.values[1] = 2; r.values[2] = 3; r.tag = 7;
  r.values[i % 3] = (uint16_t)x;
  return r.values[0] + 10u * r.values[1] + 100u * r.values[2] + r.tag;
}
uint32_t union_update(uint32_t x) {
  union word { uint32_t a; uint32_t b; } w;
  w.a = x;
  w.b += 7;
  return w.a;
}
uint32_t enum_compare(int32_t x) {
  enum sign { minus = -1, zero = 0, plus = 1 } e = (enum sign)x;
  return e < zero;
}
uint32_t local_loop(uint32_t n) {
  uint32_t acc = 0;
  while (n) { acc += n; --n; }
  return acc;
}
uint32_t shadow(uint32_t x) {
  uint32_t out = x;
  { uint32_t x = 7; out += x; }
  return out;
}
bool logical(bool x, bool y) { return !(x && y) || (x != y); }
uint32_t select_effect(uint32_t x, uint32_t y) { return x ? y / x : 99; }
uint32_t irreducible(uint32_t x, uint32_t n) {
  if (x & 1) goto b;
a:
  if (!n) return x;
  --n; x += 3;
b:
  if (!n) return x;
  --n; x ^= 7;
  goto a;
}
#ifdef __CPROVER__
uint32_t bad(uint32_t x) {
  __CPROVER_assert(x != 7, "seven is forbidden"); return x;
}
uint32_t pruned(uint32_t x) {
  __CPROVER_assume(x < 10);
  __CPROVER_assert(x <= 9, "bounded input"); return x;
}
extern uint32_t nondet_uint(void);
uint32_t constrained(void) {
  uint32_t x = nondet_uint();
  __CPROVER_assume(x < 10);
  __CPROVER_assert(x <= 9, "bounded choice"); return x;
}
uint32_t uninitialized(void) {
  uint32_t x;
  __CPROVER_assert(x == x, "stable uninitialized value"); return x;
}
uint32_t self_read(void) { uint32_t x; x = x + 1; return x; }
uint32_t read_before_write(void) { uint32_t x; uint32_t y = x; x = 0; return y; }
uint32_t bad_spin(void) {
  __CPROVER_assert(0, "before divergence");
  while (1) {}
}
#endif
