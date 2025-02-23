package client

import (
	"net"
)

// 读取字节
func ReadByte(conn net.Conn, count int) ([]byte, error) {
	result := make([]byte, count, count)
	n, err := conn.Read(result)
	if err != nil || n != count {
		return nil, err
	}

	//fmt.Printf("DEBUG: read %d bytes[%v] from conn %v\n", count, result, conn)
	return result, nil
}

// 读取以NULL结尾的字符串
func ReadNullEndString(conn net.Conn) (string, error) {
	var resultBytes []byte
	nextByte, err := ReadByte(conn, 1)
	//fmt.Printf("DEBUG: read null end string, next byte: %x\n", nextByte)
	if err != nil {
		return string(resultBytes), err
	}

	for {
		// 消费掉NULL
		if nextByte[0] == STRING_NULL {
			break
		}

		resultBytes = append(resultBytes, nextByte[0])

		nextByte, err = ReadByte(conn, 1)
		if err != nil {
			return string(resultBytes), err
		}
		//fmt.Printf("DEBUG: read null end string, next byte: %x\n", nextByte)
	}

	return string(resultBytes), nil
}
