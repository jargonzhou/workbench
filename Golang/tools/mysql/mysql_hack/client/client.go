package client

import (
	"crypto/sha1"
	"encoding/binary"
	"fmt"
	"log"
	"net"

	mysql "mysql_hack"
)

const (
	NETWORK           = "tcp"
	EOF_PACKET_HEADER = byte(0xFE)
	STRING_NULL       = byte(0x00)
)

type ClientRequest struct {
	Host     string
	Port     int
	User     string
	password string
	Database string
}

//---------------------------------------------------------------------------
// 动作
//---------------------------------------------------------------------------

func Handshake(clientRequest *ClientRequest) {
	address := fmt.Sprintf("%s:%d", clientRequest.Host, clientRequest.Port)
	log.Printf("Handshake to %s\n", address)

	// 1 init handshake
	conn, err := net.Dial(NETWORK, address)
	if err != nil {
		log.Printf("connect failed: %v", err)
		return
	}
	defer conn.Close()

	// 2 parse server handshake respone
	handshakeV10, err := ParseHandshakeV10(conn)
	if err != nil {
		log.Printf("parser handshakeV10 failed: %v", err)
		return
	}
	log.Printf("handshakeV10=%#v\n", handshakeV10)

	// 3 construct & send client handshake response
	handshakeResponse41, err := ConstructHandshakeResponse41Packet(clientRequest, handshakeV10)
	if err != nil {
		log.Printf("construct handshakeResponse41 failed: %v", err)
		return
	}

	log.Printf("send client handshake response: %#v\n", handshakeResponse41)
	_, err = conn.Write(handshakeResponse41.Bytes())
	if err != nil {
		log.Printf("send handshakeResponse41 failed: %v", err)
		return
	}

	// 4 parse handshake response
	res, err := ParsePacket(conn)
	if err != nil {
		log.Printf("send handshakeResponse41 failed: %v", err)
		return
	}
	log.Printf("res=%#v: %s\n", res, string(res.Payload))
}

//---------------------------------------------------------------------------
// 解析报文
//---------------------------------------------------------------------------

func ParseHandshakeV10(conn net.Conn) (*HandshakeV10, error) {
	result := new(HandshakeV10)

	packetHeader, err := ParsePacketHeader(conn)
	if err != nil {
		return result, err
	}
	result.PacketHeader = *packetHeader

	protocolVersion, err := ReadByte(conn, 1)
	if err != nil {
		return result, err
	}
	result.ProtocolVersion = uint8(protocolVersion[0])

	serverVersion, err := ReadNullEndString(conn)
	if err != nil {
		return result, err
	}
	result.ServerVersion = serverVersion

	threadId, err := ReadByte(conn, 4)
	if err != nil {
		return result, err
	}
	result.ThreadId = binary.LittleEndian.Uint32(threadId)

	authPluginDataPart1, err := ReadByte(conn, 8)
	if err != nil {
		return result, err
	}
	result.AuthPluginDataPart1 = authPluginDataPart1
	endAuthPluginDataPart1, err := ReadByte(conn, 1)
	if err != nil {
		return result, err
	}
	result.endAuthPluginDataPart1 = endAuthPluginDataPart1[0]

	capabilityFlags1, err := ReadByte(conn, 2)
	if err != nil {
		return result, err
	}
	result.CapabilityFlags1 = capabilityFlags1

	characterSet, err := ReadByte(conn, 1)
	if err != nil {
		return result, err
	}
	result.CharacterSet = uint8(characterSet[0])

	statusFlag, err := ReadByte(conn, 2)
	if err != nil {
		return result, err
	}
	result.StatusFlags = statusFlag

	capabilityFlags2, err := ReadByte(conn, 2)
	if err != nil {
		return result, err
	}
	result.CapabilityFlags2 = capabilityFlags2

	authPluginDataLen, err := ReadByte(conn, 1)
	if err != nil {
		return result, err
	}
	result.AuthPluginDataLen = uint8(authPluginDataLen[0])

	reserved, err := ReadByte(conn, 10)
	if err != nil {
		return result, err
	}
	result.Reserved = reserved

	authPluginDataPart2Length := uint8(13)
	if authPluginDataPart2Length < result.AuthPluginDataLen-8 {
		authPluginDataPart2Length = result.AuthPluginDataLen - 8
	}
	authPluginDataPart2, err := ReadByte(conn, int(authPluginDataPart2Length))
	if err != nil {
		return result, err
	}
	result.AuthPluginDataPart2 = authPluginDataPart2

	authPluingName, err := ReadNullEndString(conn)
	if err != nil {
		return result, err
	}
	result.AuthPluingName = string(authPluingName)

	return result, nil
}

// 解析报文头
func ParsePacketHeader(conn net.Conn) (*PacketHeader, error) {
	result := new(PacketHeader)

	payloadLength, err := ParsePacketPayloadLength(conn)
	if err != nil {
		return result, err
	}
	result.PayloadLength = payloadLength

	sequenceId, err := ReadByte(conn, 1)
	if err != nil {
		return result, err
	}
	result.SequenceId = uint8(sequenceId[0])

	return result, nil
}

// 解析报文
func ParsePacket(conn net.Conn) (*Packet, error) {
	result := new(Packet)

	packetHeader, err := ParsePacketHeader(conn)
	if err != nil {
		return result, err
	}
	result.PacketHeader = *packetHeader

	payload, err := ReadByte(conn, int(result.PayloadLength))
	if err != nil {
		return result, err
	}
	result.Payload = payload

	return result, nil
}

// 解析出报文长度: 3个字节
func ParsePacketPayloadLength(conn net.Conn) (uint32, error) {
	b := make([]byte, 3, 3)
	_, err := conn.Read(b)
	if err != nil {
		return 0, err
	}

	return uint32(b[0]) | uint32(b[1])<<8 | uint32(b[2])<<16, nil
}

//---------------------------------------------------------------------------
// 构造报文
//---------------------------------------------------------------------------

func ConstructPacketPayloadLength(length uint32) []byte {
	result := make([]byte, 3)

	_ = result[2] // early bounds check to guarantee safety of writes below
	result[0] = byte(length)
	result[1] = byte(length >> 8)
	result[2] = byte(length >> 16)

	return result
}

func ConstructPacket(payload []byte) *Packet {
	log.Printf("construct packet: %x\n", payload)
	result := &Packet{
		PacketHeader: PacketHeader{
			PayloadLength: uint32(len(payload)),
			SequenceId:    1,
		},
		Payload: payload,
	}
	return result
}

func ConstructHandshakeResponse41Packet(
	clientRequest *ClientRequest,
	handshakeV10 *HandshakeV10) (*Packet, error) {
	payload, err := ConstructHandshakeResponse41(clientRequest, handshakeV10)
	if err != nil {
		return nil, err
	}
	log.Printf("HandshakeResponse41=%#v\n", payload)

	payloadBytes, err := payload.Bytes()
	if err != nil {
		return nil, err
	}
	packet := ConstructPacket(payloadBytes)
	return packet, nil
}

func ConstructHandshakeResponse41(
	clientRequest *ClientRequest,
	handshakeV10 *HandshakeV10) (*HandshakeResponse41, error) {

	result := &HandshakeResponse41{
		ClientFlag:    []byte{0x0d, 0xa2, 0x3a, 0x00},
		MaxPacketSize: []byte{0xff, 0xff, 0xff, 0x00},
		CharacterSet:  byte(0x2d),
		Filler: []byte{
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00},
		UserName:         clientRequest.User,
		Datatabase:       clientRequest.Database,
		ClientPluginName: "mysql_native_password",
	}

	// SHA1(password)
	sha1Hash := sha1.New()
	_, err := sha1Hash.Write([]byte(clientRequest.password))
	if err != nil {
		return result, err
	}
	passwordHash := sha1Hash.Sum(nil)

	// SHA1(SHA1(password))
	sha1Hash.Reset()
	_, err = sha1Hash.Write(passwordHash)
	if err != nil {
		return result, err
	}
	passwordHashHash := sha1Hash.Sum(nil)

	// SHA1("20-bytes random data from server" < concat > SHA1(SHA1(password)))
	sha1Hash.Reset()
	authData := handshakeV10.AuthPluginData()
	authData = append(authData, passwordHashHash...)
	_, err = sha1Hash.Write(authData)
	if err != nil {
		return result, err
	}
	authDataHash := sha1Hash.Sum(nil)

	// SHA1(password) XOR SHA1("20-bytes random data from server" < concat > SHA1(SHA1(password)))
	// authResponseLength := len(passwordHash)
	// for i := 0; i < authResponseLength; i++ {
	// 	passwordHash[i] = byte(uint8(passwordHash[i]) ^ uint8(authDataHash[i]))
	// }

	result.AuthResponse = mysql.XOR(passwordHash, authDataHash)
	result.AuthResponseLength = uint8(len(result.AuthResponse))

	result.ClientConnectAttrs = ClientConnectAttrs{
		LengthOfAllKeyValues: uint8(20),
		KeyValues: []ClientConnectAttrKeyValue{
			ClientConnectAttrKeyValue{
				Key:   "clientId",
				Value: "zhoujiagen",
			},
		},
	}

	return result, nil
}
