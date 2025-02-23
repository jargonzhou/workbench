#include "../include/for.h"
#define N 10

active proctype P() {
  int sum = 0;
  FOR (i, 1, N)
    sum = sum + i
  ROF (i);
  printf("The sum of the first %d numbers = %d\n", N, sum)
}