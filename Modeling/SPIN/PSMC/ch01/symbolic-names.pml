#define N 10

mtype = { red, yellow, green };
// add new symbolic names to mtype
mtype = { green_and_yellow, yellow_and_red };
mtype light = green;

active proctype P() {
  do
  :: if
     :: light == red -> light = yellow_and_red
     :: light == yellow_and_red -> light = green
     :: light == green -> light = green_and_yellow
     :: light == green_and_yellow -> light = red
     fi
     printf("The light is now %e\n", light)
  od
}
