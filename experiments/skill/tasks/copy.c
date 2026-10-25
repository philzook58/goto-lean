/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned copy_input(unsigned x) {
    unsigned result = x;
    __CPROVER_assert(result == x, "copied value matches input");
    return result;
}
