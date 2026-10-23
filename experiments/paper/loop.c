/* arXiv:2302.02384v1, Section 5.3; CC BY 4.0. Added assert.h. */
#include <assert.h>
_Bool f(void);
int main(void) {
  for (int i = 0; i < 100; i++) {
    if (f()) break;
  }
  assert(0);
}
