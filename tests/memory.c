#include <stdint.h>
#ifdef __CPROVER__
#define CHECK(c) __CPROVER_assert(c, #c)
#else
#include <assert.h>
#define CHECK(c) assert(c)
#endif

unsigned cursor_alias(void) {
  char buf[] = "ab";
  char *p = buf;
  char **pp = &p;
  *pp = *pp + 1;
  CHECK(p == buf + 1 && *p == 'b');
  return (unsigned)*p;
}

uint32_t alias_local(uint32_t x) {
  uint32_t value = x;
  uint32_t *p = &value;
  *p += 3;
  return value;
}

uint32_t alias_bytes(uint32_t x) {
  uint32_t value = x;
  unsigned char *p = (unsigned char *)&value;
  p[1] = 0x5a;
  return value;
}

uint32_t alias_member(uint32_t x) {
  struct pair { uint8_t a; uint32_t b; } value = {7, x};
  uint32_t *p = &value.b;
  *p += value.a;
  return value.b;
}

unsigned alias_array(unsigned i, unsigned x) {
  uint16_t a[] = {11, 22, 33, 44};
  uint16_t *p = &a[i % 4];
  *p = (uint16_t)x;
  return a[i % 4];
}

unsigned one_past(void) {
  uint32_t a[4];
  uint32_t *p = a + 4;
  return (unsigned)(p - a);
}

unsigned backwards(void) {
  uint32_t a[] = {11, 22, 33, 44};
  uint32_t *p = a + 4;
  p -= 3;
  CHECK(*p == 22);
  return (unsigned)(a - (p + 2));
}

unsigned distinct_objects(void) {
  unsigned x = 3, y = 5;
  unsigned *p = &x;
  *p = 19;
  CHECK(&x != &y && y == 5);
  return x + y;
}

unsigned stable_uninitialized(void) {
  unsigned x;
  unsigned *p = &x;
  return *p == x;
}

unsigned null_bad(void) {
  unsigned *p = 0;
  return *p;
}

unsigned bounds_bad(void) {
  unsigned char a[2] = {1, 2};
  unsigned char *p = a + 2;
  return *p;
}

unsigned dead_bad(void) {
  unsigned char *p;
  { unsigned char x = 4; p = &x; }
  return *p;
}

uint32_t store_parameter(uint32_t *p, uint32_t x) {
  *p = x;
  return *p;
}

unsigned cursor_parameter(char **cursor) {
  *cursor += 1;
  return (unsigned)**cursor;
}

unsigned char *escape_local(void) {
  unsigned char x = 7;
  return &x;
}

/* Pointer subtraction must preserve the object and check its lower bound. */
unsigned offset_good(unsigned i) {
  unsigned a[2] = {11, 22};
  unsigned *p = a + 1;
  return *(p - (i % 2));
}

unsigned offset_bad(void) {
  unsigned a[2] = {11, 22};
  unsigned *p = a + 1;
  return *(p - 2);
}

/* A store through one alias must preserve a distinct object's contents. */
unsigned separate_good(unsigned x) {
  unsigned a = 0, b = 7;
  unsigned *p = &a;
  *p = x;
  CHECK(b == 7);
  return b;
}

unsigned separate_bad(unsigned x) {
  unsigned a = 0, b = 7;
  unsigned *p = &a;
  *p = x;
  CHECK(b == x); /* Deliberately false for x = 9; all accesses are defined. */
  return b;
}

#ifdef HARNESS
int main(void) {
  CHECK(cursor_alias() == 'b');
  CHECK(alias_local(9) == 12);
  CHECK(alias_bytes(0x12345678) == 0x12345a78);
  CHECK(alias_member(23) == 30);
  CHECK(alias_array(3, 12345) == 12345);
  CHECK(one_past() == 4);
  CHECK(backwards() == (unsigned)-3);
  CHECK(distinct_objects() == 24);
}
#endif

#include <stdlib.h>
unsigned heap_roundtrip(unsigned x) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  *p = x;
  unsigned result = *p;
  CHECK(result == x);
  free(p);
  return result;
}

unsigned heap_dead(unsigned x) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  *p = x;
  free(p);
  return *p; /* Negative heap control: use after free. */
}

unsigned heap_null(void) { free(0); return 1; }
unsigned heap_double_free(void) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  free(p); free(p); return 1;
}
unsigned heap_interior(void) {
  unsigned *p = malloc(2 * sizeof *p);
  if (!p) return 0;
  free(p + 1); return 1;
}
unsigned heap_bounds(void) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  p[1] = 1; free(p); return 1;
}
unsigned heap_stack(void) { unsigned x = 0; free(&x); return 1; }
unsigned heap_unchecked(void) { unsigned *p = malloc(sizeof *p); *p = 1; free(p); return 1; }

/* This caller handles both malloc outcomes through free(NULL). */
unsigned heap_release(unsigned x) {
  void *p = malloc(4);
  free(p);
  return x;
}
