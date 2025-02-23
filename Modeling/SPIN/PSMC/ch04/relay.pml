byte input, output;

active proctype Source() {
  int i;
  for (i: 1 .. 10) {
    input == 0; // wait until empty
    input = i
  }
}

active proctype Relay() {
  do
  :: atomic {
      input != 0
      output == 0;
      if
      :: output = input
      :: skip // drop input data
      fi
    }
    input = 0
  od
}

active proctype Destination() {
  do
  :: output != 0 // wait until full
    printf("Output = %d\n", output)
    output = 0
  od
}