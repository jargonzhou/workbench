#define N 10

active proctype P() {
  int sum = 0;
  int i;
  for (i: 1 .. N) {
    sum = sum + i
  }
  printf("The sum of the first %d numbers = %d\n", N, sum)
}