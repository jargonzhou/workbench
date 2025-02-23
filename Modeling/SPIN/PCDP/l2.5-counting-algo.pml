#include "include/for.h"
#define TIMES 10

byte n = 0;

proctype P() {
  byte temp;
  FOR (i, 1, TIMES)
    temp = n;
    n = temp + 1;
  ROF (i)
}

init {
  atomic {
    run P();
    run P()
  }

  (_nr_pr == 1);
  printf ("MSC: The value is %d\n", n)
}