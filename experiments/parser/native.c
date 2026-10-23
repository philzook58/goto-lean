#include <stddef.h>
#include <string.h>
#include "take_word.inc"

int parse_probe(char *input, char *out, size_t capacity, size_t *offset) {
  char *cursor = input;
  int ok = take_word(&cursor, out, capacity);
  *offset = (size_t)(cursor - input);
  return ok;
}
