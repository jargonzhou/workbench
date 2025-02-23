#define N 5

inline write(ar) {
  int k;
  d_step {
    for (k: 0 .. N-1) {
      printf("%d ", ar[k])
    }
    printf("\n")
  }
}

active proctype P() {
  int a[N];
  int i;
  write(a);
  for (i: 0 .. N-1) {
    a[i] = i
  }
  write(a)
}