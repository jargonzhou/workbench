active proctype P() {
  int a[5];
  a[0] = 0; a[1] = 10; a[2] = 20; a[3] = 30; a[4] = 40;
  int sum = 0;
  int i;
  for (i: 0 .. 4) {
    sum = sum + a[i]
  }
  printf("The sum of the numbers = %d\n", sum)
}