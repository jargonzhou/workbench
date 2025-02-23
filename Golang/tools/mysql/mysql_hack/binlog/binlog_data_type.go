package binlog

import (
	"encoding/binary"
	"errors"
	"os"
)

// 读取文件中字节
func ReadByte(file *os.File, count int) ([]byte, int, error) {
	result := make([]byte, count, count)
	n, err := file.Read(result)
	if err != nil || n != count {
		return nil, 0, err
	}
	return result, n, nil
}

// 读取文件中整数
func ReadLengthEncodedInteger(file *os.File) (size uint8, value uint64, err error) {

	firstByte, _, err := ReadByte(file, 1)
	if err != nil {
		return 0, 0, err
	}
	firstByteValue := uint64(firstByte[0])

	if firstByteValue < 0 || firstByteValue > 254 {
		_, err := file.Seek(-1, 1)
		if err != nil {
			return 0, 0, err
		}

		return 0, 0, errors.New("Parse Integer failed")
	} else if firstByteValue <= 250 { // 1-byte integer
		return 1, firstByteValue, nil
	} else if firstByteValue == 252 { // 0xFC + 2-byte integer
		valueBytes, _, err := ReadByte(file, 2)
		if err != nil {
			return 0, 0, err
		}
		return 3, uint64(binary.LittleEndian.Uint16(valueBytes)), nil
	} else if firstByteValue == 253 { // 0xFD + 3-byte integer
		valueBytes, _, err := ReadByte(file, 3)
		if err != nil {
			return 0, 0, err
		}
		_ = valueBytes[2]
		resultValue := uint32(valueBytes[0]) | uint32(valueBytes[1])<<8 | uint32(valueBytes[2])<<16
		return 4, uint64(resultValue), nil
	} else if firstByteValue == 254 { // 0xFE + 8-byte integer
		valueBytes, _, err := ReadByte(file, 8)
		if err != nil {
			return 0, 0, err
		}
		return 9, binary.LittleEndian.Uint64(valueBytes), nil
	} else {
		return 0, 0, errors.New("Parse Integer failed")
	}
}
