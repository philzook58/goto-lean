#include <stdlib.h>

/* Use each void function as the entry point, so CBMC adds its end-of-program check. */
void leak_good(void) {
  void *p = malloc(4);
  if (p) free(p);
}

void leak_bad(void) {
  void *p = malloc(4);
  (void)p; /* Deliberately lose the allocation. */
}
