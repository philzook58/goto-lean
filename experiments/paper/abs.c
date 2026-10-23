/* arXiv:2302.02384v1, Listing 1. Kroening, Schrammel, Tautschnig; CC BY 4.0. */
int abs(int x) {
  int y = x;
  if (x < 0) y = -x;
  return y;
}
