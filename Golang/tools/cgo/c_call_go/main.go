package main

import "fmt"

/*
extern int add(int a, int b);
*/
import "C" // add: defined in example.c

//export doubler
func doubler(i int) int {
	return i * 2
}

// WANR: no blank between "//" and "export"!

func main() {
	sum := C.add(3, 2) // refer add: example.c
	fmt.Println(sum)
}
