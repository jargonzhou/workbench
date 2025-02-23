byte request = 0;

active proctype Server1() {
endserver:
  do
  :: request == 1 ->
    printf("Service 1\n");
    request = 0
  od
}

active proctype Server2() {
endserver:
  do
  :: request == 2 ->
    printf("Service 2\n");
    request = 0
  od
}

active proctype Client() {
  request = 1;
  request == 0;
  request = 2;
  request == 0
}
