bool wantP = false, wantQ = false;
byte critical = 0;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    critical++;
    printf("Critical section P\n");
    assert (critical <= 1);
    critical--;
    wantP = false;
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    critical++;
    printf("Critical section Q\n");
    assert (critical <= 1);
    critical--;
    wantQ = false;
  od
}