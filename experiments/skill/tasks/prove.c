/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned toggle_twice(unsigned x, unsigned mask) {
    unsigned temp = x ^ mask;
    unsigned result = temp ^ mask;
    __CPROVER_assert(result == x, "two toggles restore input");
    return result;
}
