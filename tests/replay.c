/* Execute the original source with explicit nondeterminism and observable check outcomes. */
#include <stdint.h>
#include <setjmp.h>
static jmp_buf stopped;
static uint32_t choice;
uint32_t nondet_uint(void) { return choice; }
#define __CPROVER__ 1
#define __CPROVER_assume(p) do { if (!(p)) longjmp(stopped, 2); } while (0)
#define __CPROVER_assert(p, message) do { if (!(p)) longjmp(stopped, 1); } while (0)
#include "scalars.c"
int replay(uint32_t kind, uint32_t input, uint32_t *result) {
  int status = setjmp(stopped);
  if (status) return status;
  choice = input;
  *result = kind == 0 ? constrained() : kind == 1 ? bad(input) : pruned(input);
  return 0;
}
