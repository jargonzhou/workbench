package mysql_hack

// 字段类型
// https://github.com/mysql/mysql-server/blob/124c7ab1d6f914637521fd4463a993aa73403513/include/field_types.h
var ColumnType map[int]string

// 字段定义标志
// https://dev.mysql.com/doc/dev/mysql-server/latest/group__group__cs__column__definition__flags.html
// https://github.com/mysql/mysql-server/blob/124c7ab1d6f914637521fd4463a993aa73403513/include/mysql_com.h
var ColumnDefinitionFlags map[int]string

// 日志事件类型
// https://github.com/mysql/mysql-server/blob/124c7ab1d6f914637521fd4463a993aa73403513/sql/log_event.h
// https://github.com/mysql/mysql-server/blob/124c7ab1d6f914637521fd4463a993aa73403513/libbinlogevents/include/binlog_event.h
// https://github.com/mysql/mysql-server/blob/124c7ab1d6f914637521fd4463a993aa73403513/libbinlogevents/include/statement_events.h
var LogEventType map[int8]string

func init() {
	ColumnType = map[int]string{
		0:   "MYSQL_TYPE_DECIMAL",
		1:   "MYSQL_TYPE_TINY",
		2:   "MYSQL_TYPE_SHORT",
		3:   "MYSQL_TYPE_LONG",
		4:   "MYSQL_TYPE_FLOAT",
		5:   "MYSQL_TYPE_DOUBLE",
		6:   "MYSQL_TYPE_NULL",
		7:   "MYSQL_TYPE_TIMESTAMP",
		8:   "MYSQL_TYPE_LONGLONG",
		9:   "MYSQL_TYPE_INT24",
		10:  "MYSQL_TYPE_DATE",
		11:  "MYSQL_TYPE_TIME",
		12:  "MYSQL_TYPE_DATETIME",
		13:  "MYSQL_TYPE_YEAR",
		14:  "MYSQL_TYPE_NEWDATE", /**< Internal to MySQL. Not used in protocol */
		15:  "MYSQL_TYPE_VARCHAR",
		16:  "MYSQL_TYPE_BIT",
		17:  "MYSQL_TYPE_TIMESTAMP2",
		18:  "MYSQL_TYPE_DATETIME2", /**< Internal to MySQL. Not used in protocol */
		19:  "MYSQL_TYPE_TIME2",     /**< Internal to MySQL. Not used in protocol */
		20:  "MYSQL_TYPE_JSON",
		21:  "MYSQL_TYPE_NEWDECIMAL",
		247: "MYSQL_TYPE_ENUM",
		248: "MYSQL_TYPE_SET",
		249: "MYSQL_TYPE_TINY_BLOB",
		250: "MYSQL_TYPE_MEDIUM_BLOB",
		251: "MYSQL_TYPE_LONG_BLOB",
		252: "MYSQL_TYPE_BLOB",
		253: "MYSQL_TYPE_VAR_STRING",
		254: "MYSQL_TYPE_STRING",
		255: "MYSQL_TYPE_GEOMETRY",
	}

	ColumnDefinitionFlags = map[int]string{
		1:     "NOT_NULL_FLAG",
		2:     "PRI_KEY_FLAG",
		4:     "UNIQUE_KEY_FLAG",
		8:     "MULTIPLE_KEY_FLAG",
		16:    "BLOB_FLAG",
		32:    "UNSIGNED_FLAG",
		64:    "ZEROFILL_FLAG",
		128:   "BINARY_FLAG",
		256:   "ENUM_FLAG",
		512:   "AUTO_INCREMENT_FLAG",
		1024:  "TIMESTAMP_FLAG",
		2048:  "SET_FLAG",
		4096:  "NO_DEFAULT_VALUE_FLAG",
		8192:  "ON_UPDATE_NOW_FLAG",
		32768: "NUM_FLAG|GROUP_FLAG",
		16384: "PART_KEY_FLAG",
		// 32768:     "GROUP_FLAG",
		65536:     "UNIQUE_FLAG",
		131072:    "BINCMP_FLAG",
		262144:    "GET_FIXED_FIELDS_FLAG",
		524288:    "FIELD_IN_PART_FUNC_FLAG",
		1048576:   "FIELD_IN_ADD_INDEX",
		2097152:   "FIELD_IS_RENAMED",
		22:        "FIELD_FLAGS_STORAGE_MEDIA",
		12582912:  "FIELD_FLAGS_STORAGE_MEDIA_MASK",
		24:        "FIELD_FLAGS_COLUMN_FORMAT",
		50331648:  "FIELD_FLAGS_COLUMN_FORMAT_MASK",
		67108864:  "FIELD_IS_DROPPED",
		134217728: "EXPLICIT_NULL_FLAG",
		268435456: "FIELD_IS_MARKED",
	}

	LogEventType = map[int8]string{
		0:  "UNKNOWN_EVENT",
		1:  "START_EVENT_V3",
		2:  "QUERY_EVENT",
		3:  "STOP_EVENT",
		4:  "ROTATE_EVENT",
		5:  "INTVAR_EVENT",
		6:  "LOAD_EVENT",
		7:  "SLAVE_EVENT",
		8:  "CREATE_FILE_EVENT",
		9:  "APPEND_BLOCK_EVENT",
		10: "EXEC_LOAD_EVENT",
		11: "DELETE_FILE_EVENT",
		12: "NEW_LOAD_EVENT",
		13: "RAND_EVENT",
		14: "USER_VAR_EVENT",
		15: "FORMAT_DESCRIPTION_EVENT",
		16: "XID_EVENT",
		17: "BEGIN_LOAD_QUERY_EVENT",
		18: "EXECUTE_LOAD_QUERY_EVENT",
		19: "TABLE_MAP_EVENT",
		20: "PRE_GA_WRITE_ROWS_EVENT",
		21: "PRE_GA_UPDATE_ROWS_EVENT",
		22: "PRE_GA_DELETE_ROWS_EVENT",
		23: "WRITE_ROWS_EVENT_V1",
		24: "UPDATE_ROWS_EVENT_V1",
		25: "DELETE_ROWS_EVENT_V1",
		26: "INCIDENT_EVENT",
		27: "HEARTBEAT_LOG_EVENT",
		28: "IGNORABLE_LOG_EVENT",
		29: "ROWS_QUERY_LOG_EVENT",
		30: "WRITE_ROWS_EVENT",
		31: "UPDATE_ROWS_EVENT",
		32: "DELETE_ROWS_EVENT",
		33: "GTID_LOG_EVENT",
		34: "ANONYMOUS_GTID_LOG_EVENT",
		35: "PREVIOUS_GTIDS_LOG_EVENT",
		36: "TRANSACTION_CONTEXT_EVENT",
		37: "VIEW_CHANGE_EVENT",
		38: "XA_PREPARE_LOG_EVENT",
		39: "PARTIAL_UPDATE_ROWS_EVENT",
	}
}
