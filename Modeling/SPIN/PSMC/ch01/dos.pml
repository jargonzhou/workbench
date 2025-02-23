// GCD

active proctype P() {
  int x = 15, y = 20;
  int a = x, b = y;
  do
  :: a > b -> a = a - b
  :: b > a -> b = b - a
  :: a == b -> break
  od
  printf("The GCD of %d and %d = %d\n", x, y, a)
}