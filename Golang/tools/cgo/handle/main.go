package main

/*
#include <stdint.h>

extern void in_c(uintptr_t handle);
*/
import "C"

import (
	"fmt"
	"runtime/cgo"
)

type Person struct {
	Name string
	Age  int
}

//export processor
func processor(handle C.uintptr_t) {
	h := cgo.Handle(handle) // cast c uintptr_t to cgo.Handle
	p := h.Value().(Person) // cast handle's value to Person
	fmt.Println(p.Name, p.Age)
	h.Delete()
}

func main() {
	p := Person{
		Name: "John",
		Age:  42,
	}

	// call in_c defined in show_handle.c
	// pass c uintptr_t: cast using cgo.Handle
	C.in_c(C.uintptr_t(cgo.NewHandle(p)))
}
