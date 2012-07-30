#include <stdio.h>

/* putchard - putchar that takes a double and returns 0. */
extern double putchard(double X) {
  putchar((char)X);
  return 0;
}

/* printd - printf that takes a double prints it as "%f\n", returning 0. */
extern double printd(double X) {
  printf("%f\n", X);
  return 0;
}

/* printi - printf that takes an int prints it as "%f\n", returning 0. */
extern void printi(int X) {
  printf("%d\n", X);
  return;
}

extern void printp(int* X) {
  printf("%p\n", X);
  return;
}

extern void prints(char* X) {
  printf("%s", X);
  return;
}

/*******************************************************/
