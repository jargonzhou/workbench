package mysql_hack

import (
	"fmt"
	"testing"
)

func TestBytesToFixedLengthInteger(t *testing.T) {
	testInt1 := []byte{1}
	testInt2 := []byte{1, 2}
	testInt3 := []byte{1, 2, 3}
	testInt4 := []byte{1, 2, 3, 4}
	testInt6 := []byte{1, 2, 3, 4, 5, 6}
	testInt8 := []byte{1, 2, 3, 4, 5, 6, 7, 8}

	examples := [][]byte{
		testInt1, testInt2, testInt3, testInt4,
		testInt6, testInt8,
	}
	for _, example := range examples {
		n, value, err := BytesToFixedLengthInteger(example)
		if err != nil {
			t.Errorf("%v", err)
		}
		fmt.Printf("%d, %d\n", n, value)
	}
}

func TestFixedLengthIntegerToBytes(t *testing.T) {
	examples := []uint64{1, 513, 197121, 67305985, 6618611909121, 578437695752307201}
	for _, example := range examples {
		value := FixedLengthIntegerToBytes(example)
		fmt.Printf("%v\n", value)
	}
}

func TestBytesToLengthEncodedInteger(t *testing.T) {
	examples := [][]byte{
		// 1
		[]byte{byte(250)},
		// 3
		[]byte{byte(0xFC), byte(250), byte(250)},
		// 4
		[]byte{byte(0xFD), byte(250), byte(250), byte(250)},
		// 9
		[]byte{byte(0xFE), byte(250), byte(250), byte(250), byte(250), byte(250), byte(250), byte(250), byte(250)},
	}
	for _, example := range examples {
		n, value, err := BytesToLengthEncodedInteger(example)
		if err != nil {
			t.Errorf("%v", err)
		}
		fmt.Printf("%d, %d\n", n, value)
	}
}

func TestLengthEncodedIntegerToBytes(t *testing.T) {
	examples := []uint64{
		// 1
		250,
		// 3
		64250,
		// 4
		16448250,
		// 9
		18085043209519168250,
	}
	for _, example := range examples {
		value := LengthEncodedIntegerToBytes(example)
		fmt.Printf("%v\n", value)
	}
}

func TestNullTerminatedString(t *testing.T) {
	str := "hello, there."
	value := NullTerminatedString(str)
	fmt.Printf("%v, %v\n", []byte(str), value)
}

func TestLengthEncodedString(t *testing.T) {
	str := "hello, there."
	value := LengthEncodedString(str)
	fmt.Printf("%d, %v, %v\n", len(str), []byte(str), value)
}

func TestXOR(t *testing.T) {
	value1 := []byte{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
	value2 := []byte{11, 12, 13, 14, 15, 16, 17, 18, 19, 110}
	fmt.Printf("%v\n", XOR(value1, value2))
}
