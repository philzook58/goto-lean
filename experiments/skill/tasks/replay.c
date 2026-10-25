/* Original local skill-evaluation task, written for goto-lean, 2026-10-24. */
int signed_pick(int x, int y) {
    int selected;
    if (x < y) selected = y; else selected = x;
    return selected;
}
