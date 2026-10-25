#include <limits.h>
#include <stdlib.h>

unsigned unsigned_good(void) { unsigned x = UINT_MAX - 1; return x + 1; }
unsigned unsigned_bad(void) { unsigned x = UINT_MAX; return x + 1; }
unsigned conversion_good(void) { unsigned x = 255; return (unsigned char)x; }
unsigned conversion_bad(void) { unsigned x = 256; return (unsigned char)x; }
enum color { red = 1, blue = 3 };
unsigned enum_good(void) { enum color x = red; return x; }
unsigned enum_bad(void) { enum color x = (enum color)2; return x; }
unsigned pointer_good(void) { char a[1]; char *p = a; return p + 1 != p; }
unsigned pointer_bad(void) { char a[1]; char *p = a; return p + 8 != p; }

void cleanup_good(void) {
    void *p = malloc(1);
    if (p) free(p);
    exit(0);
}
void cleanup_bad(void) { void *p = malloc(1); (void)p; exit(0); }

static unsigned counter = 17;
static const unsigned table[] = {2, 3, 5, 7};
static const char label[] = "ok";
static const struct { unsigned left, right; } config = {7, 11};
static unsigned zeros[2];
static unsigned read_counter(void) { return counter; }
static unsigned *counter_address(void) { return &counter; }
unsigned globals_good(void) {
    unsigned *p = counter_address();
    *p = table[2];
    __CPROVER_assert(counter == 5 && read_counter() == 5, "global alias observes writes");
    counter = 23;
    __CPROVER_assert(*p == 23 && p == counter_address(), "static address survives calls");
    __CPROVER_assert(label[1] == 'k' && config.left == 7 && zeros[1] == 0,
                     "constant strings, records and zero initialization");
    return *p;
}
unsigned globals_bad(void) {
    unsigned *p = counter_address();
    *p = 5;
    __CPROVER_assert(read_counter() == 17, "global write is visible");
    return *p;
}
unsigned table_bad(void) { return table[4]; }

/* Three addressed locals need three fresh IDs beyond the two reserved encodings. */
unsigned object_capacity(void) {
    char a = 1, b = 2, c = 3;
    char *p = &a, *q = &b, *r = &c;
    __CPROVER_assert(*p + *q + *r == 6, "three distinct live objects");
    return *p + *q + *r;
}
unsigned malloc_limit(void) {
    __CPROVER_assert(__CPROVER_max_malloc_size == 8, "allocation limit follows pointer split");
    return __CPROVER_max_malloc_size == 8;
}
