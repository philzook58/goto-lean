#include <stdint.h>
#include <stddef.h>
#include <string.h>
#ifdef __CPROVER__
#define CHECK(c) __CPROVER_assert(c, #c)
#else
#include <assert.h>
#define CHECK(c) assert(c)
#endif

static unsigned leaf(unsigned x) { return x + 7; }
static void bump(unsigned *p) { *p += 3; }
void call_void(unsigned *p) { bump(p); }
unsigned nested(unsigned x) {
  unsigned value = leaf(x);
  bump(&value);
  return leaf(value);
}

struct pair { unsigned a, b; };
static struct pair make_pair(unsigned x) { return (struct pair){x, x + 1}; }
unsigned aggregate_call(unsigned x) {
  struct pair p = make_pair(x);
  return p.a ^ p.b;
}

unsigned factorial(unsigned n) {
  if (n == 0) return 1;
  return n * factorial(n - 1);
}

static unsigned odd(unsigned n);
unsigned even(unsigned n) { return n == 0 ? 1 : odd(n - 1); }
static unsigned odd(unsigned n) { return n == 0 ? 0 : even(n - 1); }

static unsigned checked(unsigned x) { CHECK(x != 7); return x; }
unsigned callee_bad(unsigned x) { return checked(x); }

static unsigned char *local_pointer(void) {
  unsigned char local = 42;
  return &local;
}
unsigned callee_dead(void) {
  unsigned char *p = local_pointer();
  return *p;
}

unsigned copy_word(unsigned x) {
  unsigned char src[] = {(unsigned char)x, (unsigned char)(x >> 8), 0};
  unsigned char dst[] = {99, 99, 99, 77};
  void *result = memcpy(dst, src, 3);
  CHECK(result == dst && dst[3] == 77);
  return dst[0] + 256u * dst[1] + 65536u * (unsigned)strlen((char *)dst);
}

unsigned copy_disjoint(void) {
  char a[] = "abc....";
  memcpy(a + 4, a, 3);
  CHECK(a[0] == 'a' && a[3] == '.' && a[7] == 0);
  return a[4] + a[5] + a[6];
}

unsigned copy_overlap(void) {
  char a[] = "abcd";
  memcpy(a + 1, a, 3);
  return a[1];
}

unsigned copy_bounds(void) {
  char src[] = "abc", dst[2];
  memcpy(dst, src, 3);
  return dst[0];
}

unsigned string_bad(void) {
  char a[] = {'a', 'b'};
  return (unsigned)strlen(a);
}

#ifdef HARNESS
int main(void) {
  CHECK(nested(9) == 26);
  CHECK(factorial(10) == 3628800);
  CHECK(even(7) == 0);
  CHECK(copy_word(25185) == 156257);
  CHECK(copy_disjoint() == 'a' + 'b' + 'c');
}
#endif
