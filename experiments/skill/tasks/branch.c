/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned cap_value(unsigned x, unsigned limit) {
    unsigned result;
    if (x < limit) result = x; else result = limit;
    __CPROVER_assert(result <= limit, "cap respects limit");
    return result;
}
