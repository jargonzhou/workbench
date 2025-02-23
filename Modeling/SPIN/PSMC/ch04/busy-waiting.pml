bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    do
    :: !wantQ -> break
    :: else -> skip
    od;
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    do
    :: !wantP -> break
    :: else -> skip
    od;
    printf("Critical section Q\n");
    wantQ = false
  od
}