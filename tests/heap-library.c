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

/* Both failure paths must leave ownership clear; success preserves the old prefix. */
unsigned library_realloc(unsigned grow) {
  unsigned char *p = malloc(2);
  if (!p) return 0;
  p[0] = 17; p[1] = 23;
  unsigned char *q = realloc(p, grow ? 4 : 1);
  if (!q) {
    __CPROVER_assert(p[0] == 17 && p[1] == 23, "failed realloc preserves old storage");
    free(p);
    return 2;
  }
  __CPROVER_assert(q[0] == 17 && (!grow || q[1] == 23), "realloc preserves prefix");
  free(q);
  return 1;
}

unsigned library_realloc_null(void) {
  void *p = realloc(0, 2);
  if (!p) return 0;
  free(p);
  return 1;
}

unsigned library_realloc_zero(void) {
  void *p = malloc(1);
  if (!p) return 0;
  void *q = realloc(p, 0);
  free(q);
  return 1;
}

unsigned library_realloc_bad(void) {
  unsigned char *p = malloc(1);
  if (!p) return 0;
  p[0] = 17;
  unsigned char *q = realloc(p, 2);
  if (!q) { free(p); return 0; }
  __CPROVER_assert(q[1] == 0, "realloc extension need not be zero");
  free(q);
  return 1;
}

unsigned library_realloc_old(void) {
  unsigned char *p = malloc(1);
  if (!p) return 0;
  p[0] = 17;
  unsigned char *q = realloc(p, 2);
  if (!q) { free(p); return 0; }
  return *p; /* Negative: realloc freed the old object. */
}

unsigned copy_padding_bad(void) {
  unsigned char src[1] = {17}, dst[2] = {0, 0};
  __CPROVER_array_copy(dst, src);
  __CPROVER_assert(dst[0] == 17, "array_copy prefix");
  __CPROVER_assert(dst[1] == 0, "array_copy padding need not retain destination bytes");
  return dst[1];
}

unsigned short_circuit(unsigned b) {
  unsigned x = 17, *p = b ? &x : 0;
  __CPROVER_assert(!b || *p == 17, "guarded or skips null read");
  __CPROVER_assert((b && *p == 17) == (b != 0), "guarded and skips null read");
  return b != 0;
}

int main(void) { return library_roundtrip(41) + library_calloc() + library_realloc(1); }
