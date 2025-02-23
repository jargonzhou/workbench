package client

import (
	"crypto/sha1"
	"fmt"
	"net"
	"testing"
	"time"

	mysql "mysql_hack"
)

func testTCP(t *testing.T) {
	conn, err := net.Dial("tcp", "127.0.0.1:3306")
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	fmt.Println(conn.RemoteAddr())
	fmt.Println(conn.LocalAddr())

	time.Sleep(time.Second * 10)
}

func testSha1(t *testing.T) {
	sha1Hash := sha1.New()
	word := []byte("hello, there")
	_, err := sha1Hash.Write(word)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	wordHash := sha1Hash.Sum(nil)
	fmt.Printf("%d, %v\n", len(wordHash), word)

	// reset to hash again
	sha1Hash.Reset()
	_, err = sha1Hash.Write(word)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	wordHash = sha1Hash.Sum(nil)
	fmt.Printf("%d, %v\n", len(wordHash), word)
}

func TestHandshake(t *testing.T) {
	clientRequest := &ClientRequest{
		Host:     "127.0.0.1",
		Port:     3306,
		User:     "root",
		password: "admin",
		Database: "test",
	}

	Handshake(clientRequest)

	time.Sleep(time.Second * 5)
}

/*
0000   02 00 00 00 45 00 00 82 00 00 40 00 40 06 00 00   ....E.....@.@...
0010   7f 00 00 01 7f 00 00 01 0c ea ff 54 1d 70 16 3c   .........êÿT.p.<
0020   64 f2 d7 34 80 18 31 d7 fe 76 00 00 01 01 08 0a   dò×4..1×þv......
0030   1c 95 2e 6d 1c 95 2e 6c 4a 00 00 00 0a 38 2e 30   ...m...lJ....8.0
0040   2e 31 31 00 2a 00 00 00 6b 62 1c 76 06 4c 65 45   .11.*...kb.v.LeE
0050   00 ff ff ff 02 00 ff c3 15 00 00 00 00 00 00 00   .ÿÿÿ..ÿÃ........
0060   00 00 00 48 41 44 36 59 44 69 72 34 16 6a 37 00   ...HAD6YDir4.j7.
0070   6d 79 73 71 6c 5f 6e 61 74 69 76 65 5f 70 61 73   mysql_native_pas
0080   73 77 6f 72 64 00                                 sword.

0000   02 00 00 00 45 00 00 a2 00 00 40 00 40 06 00 00   ....E..¢..@.@...
0010   7f 00 00 01 7f 00 00 01 ff 54 0c ea 64 f2 d7 34   ........ÿT.êdò×4
0020   1d 70 16 8a 80 18 31 d4 fe 96 00 00 01 01 08 0a   .p....1Ôþ.......
0030   1c 95 2e 6d 1c 95 2e 6d 6a 00 00 01 0d a2 3a 00   ...m...mj....¢:.
0040   ff ff ff 00 2d 00 00 00 00 00 00 00 00 00 00 00   ÿÿÿ.-...........
0050   00 00 00 00 00 00 00 00 00 00 00 00 72 6f 6f 74   ............root
0060   00 14 92 80 b9 19 ff cf d1 33 96 72 ca 44 23 62   ....¹.ÿÏÑ3.rÊD#b
0070   65 96 e7 a5 54 5d 74 65 73 74 00 6d 79 73 71 6c   e.ç¥T]test.mysql
0080   5f 6e 61 74 69 76 65 5f 70 61 73 73 77 6f 72 64   _native_password
0090   00 14 08 63 6c 69 65 6e 74 49 64 0a 7a 68 6f 75   ...clientId.zhou
00a0   6a 69 61 67 65 6e                                 jiagen
*/
func testAuthData(t *testing.T) {
	part1 := []byte{0x6b, 0x62, 0x1c, 0x76, 0x06, 0x4c, 0x65, 0x45}
	part2 := []byte{0x48, 0x41, 0x44, 0x36, 0x59, 0x44, 0x69, 0x72, 0x34, 0x16, 0x6a, 0x37}

	// SHA1(password)
	sha1Hash := sha1.New()
	_, err := sha1Hash.Write([]byte("admin"))
	if err != nil {
		t.Fatalf("%v", err)
	}
	passwordHash := sha1Hash.Sum(nil)

	// SHA1(SHA1(password))
	sha1Hash.Reset()
	_, err = sha1Hash.Write(passwordHash)
	if err != nil {
		t.Fatalf("%v", err)
	}
	passwordHashHash := sha1Hash.Sum(nil)

	// SHA1("20-bytes random data from server" < concat > SHA1(SHA1(password)))
	sha1Hash.Reset()
	authData := append(part1, part2...)
	authData = append(authData, passwordHashHash...)
	_, err = sha1Hash.Write(authData)
	if err != nil {
		t.Fatalf("%v", err)
	}
	authDataHash := sha1Hash.Sum(nil)

	// SHA1(password) XOR SHA1("20-bytes random data from server" < concat > SHA1(SHA1(password)))
	// authResponseLength := len(passwordHash)
	// for i := 0; i < authResponseLength; i++ {
	// 	passwordHash[i] = byte(uint8(passwordHash[i]) ^ uint8(authDataHash[i]))
	// }

	authData = mysql.XOR(passwordHash, authDataHash)
	fmt.Printf("%x\n", authData)
	// 92 80 b9 19 ff cf d1 33 96 72 ca 44 23 62 65 96 e7 a5 54 5d
}
