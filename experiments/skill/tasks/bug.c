/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned wrong_pick(unsigned x, unsigned y) {
    unsigned selected = x < y ? x : y;
    __CPROVER_assert(selected >= x && selected >= y, "maximum dominates inputs");
    return selected;
}
