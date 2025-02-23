#define FOR(I,low,high) \
  byte I; \
  I = low ; \
  do \
  :: ( I > high ) -> break \
  :: else ->

#define ROF(I) \
  ; I++ \
  od
