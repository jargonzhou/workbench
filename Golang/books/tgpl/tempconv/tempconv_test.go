package tempconv

import (
	"flag"
	"fmt"
	"testing"
)

func TestCToF(t *testing.T) {
	var testCases = []struct {
		c    Celsius
		want Fahrenheit
	}{
		{Celsius(0), Fahrenheit(32)},
		{Celsius(100), Fahrenheit(212)},
	}

	for _, test := range testCases {
		if test.want != CToF(test.c) {
			t.Errorf(`CToF(%s) != %s`, test.c, test.want)
		}
	}
}

func TestCelsiusFlag(t *testing.T) {
	var temp = CelsiusFlag("temp", 20.0, "the temperature")
	flag.Parse()
	fmt.Println(*temp)
}
