/* Unchanged memory examples except entry-point names; same sources as examples.c. */
int buffer_overflow(void) {
  char buffer[10];
  buffer[10] = 0;
  return 0;
}
int binsearch(int x) {
  int a[16];
  signed low = 0, high = 16;
  while (low < high) {
    signed middle = low + ((high - low) >> 1);
    if (a[middle] < x) high = middle;
    else if (a[middle] > x) low = middle + 1;
    else return middle;
  }
  return -1;
}
