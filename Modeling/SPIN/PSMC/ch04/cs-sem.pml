byte sem = 1;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    atomic { // wait
      sem > 0;
      sem--
    }
    printf("Critical section P\n");
    sem++ // signal
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    atomic { // wait
      sem > 0;
      sem--
    }
    printf("Critical section Q\n");
    sem++ // signal
  od
}
