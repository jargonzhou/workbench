package binlog

const (
	// EventHeader
	TimeStampLength    = 4
	TypeCodeLength     = 1
	ServerIdLength     = 4
	EventLength        = 4
	NextPositionLength = 4
	FlagsLength        = 2
)

// Binlog事件头部
type EventHeader struct {
	Position uint32 // 4

	TimeStamp    uint32 // 4
	TypeCode     int8   // 1
	ServerId     uint32 // 4
	EventLength  uint32 // 4
	NextPosition uint32 // 4
	Flags        []byte // 2
}

type RawEvent struct {
	EventHeader

	Body []byte
}

// 0:  "UNKNOWN_EVENT",
// 1:  "START_EVENT_V3",
// 2:  "QUERY_EVENT",
// 3:  "STOP_EVENT",
// 4:  "ROTATE_EVENT",
// 5:  "INTVAR_EVENT",
// 6:  "LOAD_EVENT",
// 7:  "SLAVE_EVENT",
// 8:  "CREATE_FILE_EVENT",
// 9:  "APPEND_BLOCK_EVENT",
// 10: "EXEC_LOAD_EVENT",
// 11: "DELETE_FILE_EVENT",
// 12: "NEW_LOAD_EVENT",
// 13: "RAND_EVENT",
// 14: "USER_VAR_EVENT",
// 15: "FORMAT_DESCRIPTION_EVENT",
type FormatDescriptionEvent struct {
	// Header
	EventHeader

	// Body
	BinlogVersion   []byte // 2
	ServerVersion   []byte // 50
	CreateTimeStamp uint32 // 4
	HeaderLength    int8   // 1
	Body            []byte // NextPosition - CURRENT_POSITION
}

// 16: "XID_EVENT",
// 17: "BEGIN_LOAD_QUERY_EVENT",
// 18: "EXECUTE_LOAD_QUERY_EVENT",
// 19: "TABLE_MAP_EVENT",
// https://dev.mysql.com/doc/dev/mysql-server/latest/classbinary__log_1_1Table__map__event.html

type TableMapEvent struct {
	// Header
	EventHeader

	// Body
	TableId             []byte // 6
	Reserved            []byte // 2
	DatabaseNameLength  uint64 // variable
	DatabaseName        string // DatabaseNameLength
	endOfDatabaseName   byte   // 1
	TableNameLength     uint64 // variable
	TableName           string // TableNameLength
	endOfTableName      byte   // 1
	NumberOfColumns     uint8  // 1
	ColumnTypes         []byte // NumberOfColumns, 见ColumnType
	MetadataLength      uint64 // variable
	Metadata            []byte // MetadataLength
	ByteSizeForNullBits uint8  // integer of (NumberOfColumns + 7) / 8
	NullBits            []byte // ByteSizeForNullBits
	MetadataFields      []byte // 可选: NextPosition - CURRENT_POSITION
}

// 20: "PRE_GA_WRITE_ROWS_EVENT",
// 21: "PRE_GA_UPDATE_ROWS_EVENT",
// 22: "PRE_GA_DELETE_ROWS_EVENT",
// 23: "WRITE_ROWS_EVENT_V1",
// 24: "UPDATE_ROWS_EVENT_V1",
// 25: "DELETE_ROWS_EVENT_V1",
// 26: "INCIDENT_EVENT",
// 27: "HEARTBEAT_LOG_EVENT",
// 28: "IGNORABLE_LOG_EVENT",
// 29: "ROWS_QUERY_LOG_EVENT",
// 30: "WRITE_ROWS_EVENT",

type WriteRowsEvent struct {
	// Header
	EventHeader

	// Body
	TableId                   []byte // 4
	Reserved                  []byte // 2
	NumberOfColumns           uint8  // 1
	NumberOfBytesForBitColumn uint8  // integer of (NumberOfColumns+7)/8
	BitColumns                []byte // NumberOfBytesForBitColumn
	Skip                      byte   // 1
	Body                      []byte // NextPosition - CURRENT_POSITION
}

// 31: "UPDATE_ROWS_EVENT",
// 32: "DELETE_ROWS_EVENT",
// 33: "GTID_LOG_EVENT",
// 34: "ANONYMOUS_GTID_LOG_EVENT",
// 35: "PREVIOUS_GTIDS_LOG_EVENT",
// 36: "TRANSACTION_CONTEXT_EVENT",
// 37: "VIEW_CHANGE_EVENT",
// 38: "XA_PREPARE_LOG_EVENT",
// 39: "PARTIAL_UPDATE_ROWS_EVENT",
