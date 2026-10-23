#include <stddef.h>
#include <string.h>

/*@ requires 0 < n < capacity;
    requires \valid(out + (0 .. capacity-1));
    requires \valid_read(start + (0 .. n-1));
    requires \separated(out + (0 .. capacity-1), start + (0 .. n-1));
    assigns out[0 .. n];
    ensures out[n] == 0;
    ensures \forall integer i; 0 <= i < n ==> out[i] == \old(start[i]);
*/
static void copy_word(char *out, const char *start, size_t n, size_t capacity) {
    (void)capacity;
    memcpy(out, start, n);
    out[n] = 0;
}


static int take_word(char **cursor, char *out, size_t capacity) {
    char *p = *cursor;
    while (*p == ' ') ++p;
    char *start = p;
    while (*p && *p != ' ') ++p;
    size_t n = (size_t)(p - start);
    if (!n || n >= capacity) return 0;
    copy_word(out, start, n, capacity);
    while (*p == ' ') ++p;
    *cursor = p;
    return 1;
}

int main(void) {
    char input[] = "  hi there";
    char output[16];
    char *cursor = input;
    return take_word(&cursor, output, sizeof output);
}

