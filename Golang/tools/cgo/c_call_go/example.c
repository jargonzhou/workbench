#include "_cgo_export.h"

int add(int a, int b) {
  int doubleA = doubler(a); // doubler: go function in main.go
  int sum = doubleA + b;
  return sum;
}