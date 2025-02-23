package binlog

import (
	"encoding/binary"
	"fmt"
	"os"
)

const (
	MagicNumberLength = 4
)

func OpenBinlog(file string) *os.File {
	f, err := os.OpenFile(file, os.O_RDONLY, 0755)
	if err != nil {
		fmt.Errorf("open binlog failed: %v", err)
		return nil
	}
	return f
}

func CloseBinlog(file *os.File) {
	if file == nil {
		return
	}

	err := file.Close()
	if err != nil {
		fmt.Errorf("close binlog failed: %v", err)
		return
	}
}

// 获取文件大小
func Size(file *os.File) (int64, error) {
	fileInfo, err := file.Stat()
	if err != nil {
		fmt.Errorf("read binlog stat failed: %v", err)
		return 0, err
	}
	return fileInfo.Size(), nil
}

// 获取文件当前位置
func CurrentPosition(file *os.File) (int64, error) {
	result, err := file.Seek(0, 1)
	if err != nil {
		fmt.Errorf("read binlog current position failed: %v", err)
		return 0, err
	}
	return result, nil
}

// 读取文件的魔法数
func ReadMagicNumber(file *os.File) ([]byte, error) {
	result, _, err := ReadByte(file, MagicNumberLength)
	if err != nil {
		fmt.Errorf("read binlog magic number failed: %v", err)
		return nil, err
	}
	return result, nil
}

// 读取事件的头部
func ReadEventHeader(file *os.File) (*EventHeader, error) {
	result := new(EventHeader)

	currentPosition, err := CurrentPosition(file)
	if err != nil {
		return result, err
	}
	result.Position = uint32(currentPosition)

	timestamp, _, err := ReadByte(file, TimeStampLength)
	if err != nil {
		return result, err
	}
	result.TimeStamp = binary.LittleEndian.Uint32(timestamp)

	typeCode, _, err := ReadByte(file, TypeCodeLength)
	if err != nil {
		return result, err
	}
	result.TypeCode = int8(typeCode[0])

	serverId, _, err := ReadByte(file, ServerIdLength)
	if err != nil {
		return result, err
	}
	result.ServerId = binary.LittleEndian.Uint32(serverId)

	eventLength, _, err := ReadByte(file, EventLength)
	if err != nil {
		return result, err
	}
	result.EventLength = binary.LittleEndian.Uint32(eventLength)

	nextPosition, _, err := ReadByte(file, NextPositionLength)
	if err != nil {
		return result, err
	}
	result.NextPosition = binary.LittleEndian.Uint32(nextPosition)

	flags, _, err := ReadByte(file, FlagsLength)
	if err != nil {
		return result, err
	}
	result.Flags = flags

	return result, nil
}

func ReadRawEvent(file *os.File, header *EventHeader) (*RawEvent, error) {
	result := new(RawEvent)
	result.EventHeader = *header

	currentPosition, err := CurrentPosition(file)
	if err != nil {
		return result, err
	}
	bodyLength := int64(header.NextPosition) - currentPosition
	body, _, err := ReadByte(file, int(bodyLength))
	if err != nil {
		return result, err
	}
	result.Body = body

	return result, nil
}

// 解析格式化描述事件: 从头部开始
func ReadFormatDescriptionEvent(file *os.File) (*FormatDescriptionEvent, error) {
	result := new(FormatDescriptionEvent)

	header, err := ReadEventHeader(file)
	if err != nil {
		return result, err
	}
	result.EventHeader = *header

	binlogVersion, _, err := ReadByte(file, 2)
	if err != nil {
		return result, err
	}
	result.BinlogVersion = binlogVersion

	serverVersion, _, err := ReadByte(file, 50)
	if err != nil {
		return result, err
	}
	result.ServerVersion = serverVersion

	createTimeStamp, _, err := ReadByte(file, 4)
	if err != nil {
		return result, err
	}
	result.CreateTimeStamp = binary.LittleEndian.Uint32(createTimeStamp)

	headerLength, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.HeaderLength = int8(headerLength[0])

	currentPosition, err := CurrentPosition(file)
	if err != nil {
		return result, err
	}
	bodyLength := result.NextPosition - uint32(currentPosition)
	body, _, err := ReadByte(file, int(bodyLength))
	if err != nil {
		return result, err
	}
	result.Body = body

	return result, nil
}

// 解析表映射事件
func ReadTableMapEvent(file *os.File, header *EventHeader) (*TableMapEvent, error) {
	result := new(TableMapEvent)

	if header == nil {
		header, err := ReadEventHeader(file)
		if err != nil {
			return result, err
		}
		result.EventHeader = *header
	} else {
		result.EventHeader = *header
	}

	tableId, _, err := ReadByte(file, 6)
	if err != nil {
		return result, err
	}
	result.TableId = tableId

	reserved, _, err := ReadByte(file, 2)
	if err != nil {
		return result, err
	}
	result.Reserved = reserved

	_, databaseNameLength, err := ReadLengthEncodedInteger(file)
	if err != nil {
		return result, err
	}
	result.DatabaseNameLength = databaseNameLength
	databaseName, _, err := ReadByte(file, int(databaseNameLength))
	if err != nil {
		return result, err
	}
	result.DatabaseName = string(databaseName)
	endOfDatabaseName, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.endOfDatabaseName = endOfDatabaseName[0]

	_, tableNameLength, err := ReadLengthEncodedInteger(file)
	if err != nil {
		return result, err
	}
	result.TableNameLength = tableNameLength
	tableName, _, err := ReadByte(file, int(tableNameLength))
	if err != nil {
		return result, err
	}
	result.TableName = string(tableName)
	endOfTableName, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.endOfTableName = endOfTableName[0]

	numberOfColumn, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.NumberOfColumns = uint8(numberOfColumn[0])
	columnTypes, _, err := ReadByte(file, int(result.NumberOfColumns))
	if err != nil {
		return result, err
	}
	result.ColumnTypes = columnTypes

	_, metadataLength, err := ReadLengthEncodedInteger(file)
	if err != nil {
		return result, err
	}
	result.MetadataLength = metadataLength
	metadata, _, err := ReadByte(file, int(result.MetadataLength))
	result.Metadata = metadata

	result.ByteSizeForNullBits = uint8((result.NumberOfColumns + 7) / 8)
	nullBits, _, err := ReadByte(file, int(result.ByteSizeForNullBits))
	if err != nil {
		return result, err
	}
	result.NullBits = nullBits

	currentPosition, err := CurrentPosition(file)
	if err != nil {
		return result, err
	}
	metadataFiledsLength := int64(header.NextPosition) - currentPosition
	if metadataFiledsLength > 0 {
		metadataFields, _, err := ReadByte(file, int(metadataFiledsLength))
		if err != nil {
			return result, err
		}
		result.MetadataFields = metadataFields
	}

	return result, nil
}

// 解析写行事件
func ReadWriteRowsEvent(file *os.File, header *EventHeader) (*WriteRowsEvent, error) {
	result := new(WriteRowsEvent)

	if header == nil {
		header, err := ReadEventHeader(file)
		if err != nil {
			return result, err
		}
		result.EventHeader = *header
	} else {
		result.EventHeader = *header
	}

	tableId, _, err := ReadByte(file, 4)
	if err != nil {
		return result, err
	}
	result.TableId = tableId

	reserved, _, err := ReadByte(file, 2)
	if err != nil {
		return result, err
	}
	result.Reserved = reserved

	numberOfColumn, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.NumberOfColumns = uint8(numberOfColumn[0])
	numberOfBytesForBitColumn := uint8((result.NumberOfColumns + 7) / 8)
	result.NumberOfBytesForBitColumn = numberOfBytesForBitColumn

	bitColumns, _, err := ReadByte(file, int(result.NumberOfBytesForBitColumn))
	if err != nil {
		return result, err
	}
	result.BitColumns = bitColumns

	skip, _, err := ReadByte(file, 1)
	if err != nil {
		return result, err
	}
	result.Skip = skip[0]

	currentPosition, err := CurrentPosition(file)
	if err != nil {
		return result, err
	}
	leftLength := int64(header.NextPosition) - currentPosition
	if leftLength > 0 {
		body, _, err := ReadByte(file, int(leftLength))
		if err != nil {
			return result, err
		}
		result.Body = body
	}
	return result, nil
}
