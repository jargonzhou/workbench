package client

import (
	"bytes"
	"log"

	mysql "mysql_hack"
)

type PacketHeader struct {
	PayloadLength uint32 // 3, FixedLengthInteger
	SequenceId    uint8  // 1
}

type Packet struct {
	PacketHeader

	Payload []byte // PayloadLength
}

func (packet *Packet) Bytes() []byte {
	var result []byte = ConstructPacketPayloadLength(packet.PayloadLength)
	result = append(result, byte(packet.SequenceId))
	result = append(result, packet.Payload...)
	return result
}

type ERRPacket struct {
	Header       uint16 // 2
	ErrorCode    uint16 // 2
	ErrorMessage []byte // ???
}

type EOFPacket struct {
	PayloadLength uint32 // 3
	SequenceId    uint8  // 1

	Header      uint8  // 1
	Warning     uint16 // 2
	StatusFlags uint16 // 2
}

// https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_connection_phase_packets_protocol_handshake_v10.html
type HandshakeV10 struct {
	// Header
	PacketHeader

	// Payload
	ProtocolVersion        uint8  // 1
	ServerVersion          string // NULL end string
	ThreadId               uint32 // 4
	AuthPluginDataPart1    []byte // 8
	endAuthPluginDataPart1 byte   // 1
	CapabilityFlags1       []byte // 2
	CharacterSet           uint8  //  1
	StatusFlags            []byte // 2
	CapabilityFlags2       []byte // 2
	AuthPluginDataLen      uint8  // 1
	Reserved               []byte // 10
	AuthPluginDataPart2    []byte // max(13, AuthPluginDataLen - 8)
	AuthPluingName         string // NULL end string
}

func (packet *HandshakeV10) AuthPluginData() []byte {
	log.Printf("AuthPluginDataPart1=%#v, len=%d", packet.AuthPluginDataPart1, len(packet.AuthPluginDataPart1))
	log.Printf("AuthPluginDataPart2=%#v, len=%d", packet.AuthPluginDataPart2, len(packet.AuthPluginDataPart2))
	var result []byte = packet.AuthPluginDataPart1
	result = append(result, packet.AuthPluginDataPart2[:len(packet.AuthPluginDataPart2)-1]...)
	log.Printf("AuthPluginData=%#v, len=%d", result, len(result))
	return result
}

type HandshakeResponse41 struct {
	ClientFlag    []byte // 4
	MaxPacketSize []byte // 4
	CharacterSet  byte   // 1
	Filler        []byte // 23: all 0
	UserName      string // NULL end string
	// capabilities & CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA
	AuthResponseLength uint8 // 1
	// SHA1(password) XOR SHA1("20-bytes random data from server" < concat > SHA1(SHA1(password)))
	AuthResponse []byte // AuthResponseLength
	// capabilities & CLIENT_CONNECT_WITH_DB
	Datatabase string // NULL end string
	// capabilities & CLIENT_PLUGIN_AUTH
	ClientPluginName string // NULL end string

	//capabilities & CLIENT_CONNECT_ATTRS
	ClientConnectAttrs
}

func (packet *HandshakeResponse41) Bytes() ([]byte, error) {
	var buffer bytes.Buffer
	var err error
	_, err = buffer.Write(packet.ClientFlag)
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(packet.MaxPacketSize)
	if err != nil {
		return buffer.Bytes(), err
	}
	err = buffer.WriteByte(packet.CharacterSet)
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(packet.Filler)
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(mysql.NullTerminatedString(packet.UserName))
	if err != nil {
		return buffer.Bytes(), err
	}
	log.Printf("serial AuthResponseLength: %d\n", packet.AuthResponseLength)
	err = buffer.WriteByte(byte(packet.AuthResponseLength))
	if err != nil {
		return buffer.Bytes(), err
	}
	log.Printf("serial AuthResponse: %x\n", packet.AuthResponse)
	_, err = buffer.Write(packet.AuthResponse)
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(mysql.NullTerminatedString(packet.Datatabase))
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(mysql.NullTerminatedString(packet.ClientPluginName))
	if err != nil {
		return buffer.Bytes(), err
	}
	clientConnectAttrsBytes, err := packet.ClientConnectAttrs.Bytes()
	if err != nil {
		return buffer.Bytes(), err
	}
	_, err = buffer.Write(clientConnectAttrsBytes)
	if err != nil {
		return buffer.Bytes(), err
	}

	return buffer.Bytes(), nil
}

type ClientConnectAttrs struct {
	LengthOfAllKeyValues uint8 // LengthEncodedInteger
	KeyValues            []ClientConnectAttrKeyValue
}

func (attrs ClientConnectAttrs) Bytes() ([]byte, error) {
	var buffer bytes.Buffer

	var err error
	_, err = buffer.Write(mysql.LengthEncodedIntegerToBytes(uint64(attrs.LengthOfAllKeyValues)))
	if err != nil {
		return buffer.Bytes(), err
	}
	for _, kv := range attrs.KeyValues {
		_, err = buffer.Write(mysql.LengthEncodedString(kv.Key))
		if err != nil {
			return buffer.Bytes(), err
		}
		_, err = buffer.Write(mysql.LengthEncodedString(kv.Value))
		if err != nil {
			return buffer.Bytes(), err
		}
	}

	return buffer.Bytes(), nil

}

type ClientConnectAttrKeyValue struct {
	Key   string // LengthEncodedString
	Value string // LengthEncodedString
}
