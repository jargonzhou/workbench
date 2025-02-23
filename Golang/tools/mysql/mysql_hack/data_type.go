package mysql_hack

import (
	"encoding/binary"
	"errors"
	"math"
	"math/big"
)

const (
	BYTE_ZERO         = byte(0)
	BYTE_THREE_PREFIX = byte(0xFC) // 252
	BYTE_FOUR_PREFIX  = byte(0xFD)
	BYTE_NINE_PREFIX  = byte(0xFE)

	MAX_UINT_8  = math.MaxUint8
	MAX_UINT_16 = math.MaxUint16
	MAX_UINT_24 = 1<<24 - 1 //
	MAX_UINT_32 = math.MaxUint32
	MAX_UINT_48 = 1<<48 - 1 //
	MAX_UINT_64 = math.MaxUint64
)

//---------------------------------------------------------------------------
// 整数
//---------------------------------------------------------------------------

// unsigned integer with the least significant byte first:
// int<1>,int<2>,int<3>,int<4>,int<6>,int<8>
func BytesToFixedLengthInteger(value []byte) (uint8, uint64, error) {
	if value == nil || len(value) == 0 {
		return 0, 0, errors.New("Parse FixedLengthInteger failed")
	}
	valueLength := uint8(len(value))
	switch valueLength {
	case 1:
		return valueLength, uint64(binary.LittleEndian.Uint16(append(value[0:1], BYTE_ZERO))), nil
	case 2:
		return valueLength, uint64(binary.LittleEndian.Uint16(value[0:2])), nil
	case 3:
		return valueLength, uint64(binary.LittleEndian.Uint32(append(value[0:3], BYTE_ZERO))), nil
	case 4:
		return valueLength, uint64(binary.LittleEndian.Uint32(value[0:4])), nil
	case 6:
		return valueLength, binary.LittleEndian.Uint64(append(value[0:6], BYTE_ZERO, BYTE_ZERO)), nil
	case 8:
		return valueLength, binary.LittleEndian.Uint64(value[0:8]), nil
	default:
		return 0, 0, errors.New("Parse FixedLengthInteger failed")
	}
}

func FixedLengthIntegerToBytes(value uint64) []byte {
	var result []byte

	if value <= MAX_UINT_8 {
		result = make([]byte, 1)
		result[0] = byte(value)
	} else if value <= MAX_UINT_16 {
		result = make([]byte, 2)
		binary.LittleEndian.PutUint16(result, uint16(value))
	} else if value <= MAX_UINT_24 {
		result = make([]byte, 3)
		_ = result[2] // early bounds check to guarantee safety of writes below
		result[0] = byte(value)
		result[1] = byte(value >> 8)
		result[2] = byte(value >> 16)
	} else if value <= MAX_UINT_32 {
		result = make([]byte, 4)
		binary.LittleEndian.PutUint32(result, uint32(value))
	} else if value <= MAX_UINT_48 {
		result = make([]byte, 6)
		_ = result[5] // early bounds check to guarantee safety of writes below
		result[0] = byte(value)
		result[1] = byte(value >> 8)
		result[2] = byte(value >> 16)
		result[3] = byte(value >> 24)
		result[4] = byte(value >> 32)
		result[5] = byte(value >> 40)
	} else if value <= MAX_UINT_64 {
		result = make([]byte, 8)
		binary.LittleEndian.PutUint64(result, value)
	} else {
		return nil
	}

	return result
}

// [0, 251): 1-byte integer
// [251, 2^16): 0xFC + 2-byte integer
// [2^16, 2^24): 0xFD + 3-byte integer
// [2^24, 2^64): 0xFE + 8-byte integer
func BytesToLengthEncodedInteger(value []byte) (uint8, uint64, error) {
	if value == nil || len(value) < 1 {
		return 0, 0, errors.New("Parse LengthEncodedInteger1 failed")
	}

	firstByte := value[0]
	firstByteValue := uint64(firstByte)

	if firstByteValue >= 0 && firstByteValue <= 250 { // 1-byte integer
		return 1, firstByteValue, nil
	} else if firstByteValue == 252 { // 0xFC + 2-byte integer
		if len(value) < 3 {
			return 0, 0, errors.New("Parse LengthEncodedInteger3 failed")
		}
		return 3, uint64(binary.LittleEndian.Uint16(append(value[1:3], BYTE_ZERO))), nil
	} else if firstByteValue == 253 { // 0xFD + 3-byte integer
		if len(value) < 4 {
			return 0, 0, errors.New("Parse LengthEncodedInteger4 failed")
		}
		_ = value[3]
		resultValue := uint32(value[1]) | uint32(value[2])<<8 | uint32(value[3])<<16
		return 4, uint64(resultValue), nil
	} else if firstByteValue == 254 { // 0xFE + 8-byte integer
		if len(value) < 9 {
			return 0, 0, errors.New("Parse LengthEncodedInteger9 failed")
		}
		return 9, binary.LittleEndian.Uint64(value[1:]), nil
	} else {
		return 0, 0, errors.New("Parse LengthEncodedInteger failed")
	}
}

func LengthEncodedIntegerToBytes(value uint64) []byte {
	var result []byte
	if value < 251 {
		result = []byte{byte(value)}
	} else if value <= MAX_UINT_16 {
		result = []byte{BYTE_THREE_PREFIX}
		valueBytes := make([]byte, 2)
		binary.LittleEndian.PutUint16(valueBytes, uint16(value))
		result = append(result, valueBytes...)
	} else if value <= MAX_UINT_24 {
		result = []byte{BYTE_FOUR_PREFIX}
		valueBytes := make([]byte, 3)
		valueBytes[0] = byte(value)
		valueBytes[1] = byte(value >> 8)
		valueBytes[2] = byte(value >> 16)
		result = append(result, valueBytes...)
	} else if value <= MAX_UINT_64 {
		result = []byte{BYTE_NINE_PREFIX}
		valueBytes := make([]byte, 8)
		binary.LittleEndian.PutUint64(valueBytes, value)
		result = append(result, valueBytes...)
	} else {
		return nil
	}

	return result
}

/**
func (littleEndian) PutUint64(b []byte, v uint64) {
	_ = b[7] // early bounds check to guarantee safety of writes below
	b[0] = byte(v)
	b[1] = byte(v >> 8)
	b[2] = byte(v >> 16)
	b[3] = byte(v >> 24)
	b[4] = byte(v >> 32)
	b[5] = byte(v >> 40)
	b[6] = byte(v >> 48)
	b[7] = byte(v >> 56)
}

func (littleEndian) Uint64(b []byte) uint64 {
	_ = b[7] // bounds check hint to compiler; see golang.org/issue/14808
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}
*/

func XOR(value1, value2 []byte) []byte {
	var b1, b2, result big.Int
	return result.Xor(b1.SetBytes(value1), b2.SetBytes(value2)).Bytes()
}

//---------------------------------------------------------------------------
// 字符串
//---------------------------------------------------------------------------

func NullTerminatedString(str string) []byte {
	return append([]byte(str), BYTE_ZERO)
}

func LengthEncodedString(str string) []byte {
	return append(LengthEncodedIntegerToBytes(uint64(len(str))), []byte(str)...)
}
