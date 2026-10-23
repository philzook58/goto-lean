/* arXiv:2302.02384v1, Listing 7; CC BY 4.0. ASCII quotes replace PDF typography. */
#include <stdio.h>
int main(int argc, char **argv) {
  char password[8] = {'s','e','c','r','e','t','!','\0'};
  char buffer[16] = {'\0', };
  int tmp;
  int index = 0;
  printf("Enter your name: ");
  while ((tmp = getchar()) != '\n') {
    buffer[index] = tmp;
    ++index;
  }
  printf("%s\n", buffer);
  return 0;
}
