/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned add_small(unsigned x) {
    __CPROVER_assume(x < 100);
    unsigned result = x + 7;
    __CPROVER_assert(result < 107 && result >= x, "small addition stays in range");
    return result;
}
