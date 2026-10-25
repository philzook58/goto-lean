/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
unsigned drain(unsigned remaining) {
    while (remaining != 0) --remaining;
    __CPROVER_assert(remaining == 0, "drained");
    return remaining;
}
