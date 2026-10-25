/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
extern unsigned nondet_uint(void);
unsigned bounded_pick(void) {
    unsigned value = nondet_uint();
    __CPROVER_assume(value < 16);
    __CPROVER_assert(value < 16, "chosen value respects source bound");
    return value;
}
