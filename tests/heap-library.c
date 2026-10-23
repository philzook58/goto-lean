#include <stdlib.h>

/* Translate with --add-library: these exercise CBMC's bodies, not external stubs. */
unsigned library_roundtrip(unsigned x) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  *p = x;
  unsigned result = *p;
  __CPROVER_assert(result == x, "heap roundtrip");
  free(p);
  return result;
}

unsigned library_calloc(void) {
  unsigned *p = calloc(2, sizeof *p);
  if (!p) return 0;
  __CPROVER_assert(p[0] == 0 && p[1] == 0, "calloc initializes every byte");
  free(p);
  return 1;
}

unsigned library_calloc_overflow(void) {
  void *p = calloc((size_t)-1, 2);
  __CPROVER_assert(p == 0, "calloc rejects size overflow");
  return 1;
}

unsigned library_double_free(void) {
  void *p = malloc(1);
  if (!p) return 0;
  free(p);
  free(p);
  return 1;
}

unsigned library_dead(void) {
  unsigned *p = malloc(sizeof *p);
  if (!p) return 0;
  *p = 41;
  free(p);
  return *p;
}

/* The primitive always succeeds; its flag selects zero or arbitrary bytes. */
unsigned primitive_zero(void) {
  unsigned char *p = __CPROVER_allocate(2, 1);
  __CPROVER_assert(p != 0 && p[0] == 0 && p[1] == 0, "zero allocation");
  __CPROVER_assert(__CPROVER_r_ok(p + 2, 0) && !__CPROVER_r_ok(p + 2, 1), "one-past range");
  __CPROVER_assert(__CPROVER_w_ok(p, 2) && __CPROVER_rw_ok(p, 2), "writable range");
  return p[1];
}

unsigned primitive_null(void) {
  __CPROVER_assert(!__CPROVER_r_ok((void *)0, 0), "null is not readable even for zero bytes");
  return 1;
}

unsigned primitive_stable(void) {
  unsigned char *p = __CPROVER_allocate(1, 0);
  unsigned x = *p;
  __CPROVER_assert(*p == x, "arbitrary bytes remain stable");
  return x;
}

unsigned primitive_bad(void) {
  unsigned char *p = __CPROVER_allocate(1, 0);
  __CPROVER_assert(*p == 0, "arbitrary bytes need not be zero");
  return *p;
}

int main(void) { return library_roundtrip(41) + library_calloc(); }
