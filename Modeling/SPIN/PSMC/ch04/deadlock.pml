bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    !wantQ;
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    !wantP;
    printf("Critical section Q\n");
    wantQ = false
  od
}