package main

import "fmt"

/*
#cgo LDFLAGS: -lm
#include <stdio.h>
#include <math.h>
#include <mylib.h>

int add(int a, int b) {
	int sum = a + b;
	printf("a: %d, b: %d, sum %d\n", a, b, sum);
	return sum;
}
*/
import "C" // C: an automatically generated package

func main() {
	sum := C.add(3, 2) // refer add: C code embedded in comments
	fmt.Println(sum)
	fmt.Println(C.sqrt(100))        // refer sqrt: math.h
	fmt.Println(C.multiply(10, 20)) // refer multiply: mylib.h

	// can also refer types: C.int, C.char, C.CString
}
