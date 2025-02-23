package binlog

import (
	"fmt"
	"os"
	"testing"

	mysql "mysql_hack"
)

func TestParser(t *testing.T) {
	file := OpenBinlog("/Users/zhoujiagen/Downloads/binlog/binlog.000050")
	fileSize, err := Size(file)
	if err != nil {
		t.Fatalf("%v", err)
	}
	fmt.Println(fileSize)

	magicNumber, err := ReadMagicNumber(file)
	fmt.Printf("Magic Number: %q\n", magicNumber)

	fde, err := ReadFormatDescriptionEvent(file)
	if err != nil {
		t.Fatalf("%v", err)
	}
	fmt.Printf("%+v\n", fde)

	nextPosition := fde.NextPosition
	for {
		if int64(nextPosition) >= fileSize {
			break
		}

		eventHeader, err := ReadEventHeader(file)
		if err != nil {
			t.Fatalf("%v", err)
		}
		nextPosition = eventHeader.NextPosition
		fmt.Printf("%-30s: %+v ", mysql.LogEventType[eventHeader.TypeCode], eventHeader)

		switch eventHeader.TypeCode {
		case 0: //   "UNKNOWN_EVENT"

			printEventBody(t, file, eventHeader)
		case 1: //   "START_EVENT_V3"

			printEventBody(t, file, eventHeader)
		case 2: //   "QUERY_EVENT"

			printEventBody(t, file, eventHeader)
		case 3: //   "STOP_EVENT"

			printEventBody(t, file, eventHeader)
		case 4: //   "ROTATE_EVENT"

			printEventBody(t, file, eventHeader)
		case 5: //   "INTVAR_EVENT"

			printEventBody(t, file, eventHeader)
		case 6: //   "LOAD_EVENT"

			printEventBody(t, file, eventHeader)
		case 7: //   "SLAVE_EVENT"

			printEventBody(t, file, eventHeader)
		case 8: //   "CREATE_FILE_EVENT"

			printEventBody(t, file, eventHeader)
		case 9: //   "APPEND_BLOCK_EVENT"

			printEventBody(t, file, eventHeader)
		case 10: //  "EXEC_LOAD_EVENT"

			printEventBody(t, file, eventHeader)
		case 11: //  "DELETE_FILE_EVENT"

			printEventBody(t, file, eventHeader)
		case 12: //  "NEW_LOAD_EVENT"

			printEventBody(t, file, eventHeader)
		case 13: //  "RAND_EVENT"

			printEventBody(t, file, eventHeader)
		case 14: //  "USER_VAR_EVENT"

			printEventBody(t, file, eventHeader)
		case 15: //  "FORMAT_DESCRIPTION_EVENT"

			printEventBody(t, file, eventHeader)
		case 16: //  "XID_EVENT"

			printEventBody(t, file, eventHeader)
		case 17: //  "BEGIN_LOAD_QUERY_EVENT"

			printEventBody(t, file, eventHeader)
		case 18: //  "EXECUTE_LOAD_QUERY_EVENT"

			printEventBody(t, file, eventHeader)
		case 19: //  "TABLE_MAP_EVENT"
			tableMapEvent, err := ReadTableMapEvent(file, eventHeader)
			if err != nil {
				t.Fatalf("%v", err)
			}
			fmt.Printf("%+v\n", tableMapEvent)
		case 20: //  "PRE_GA_WRITE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		case 21: //  "PRE_GA_UPDATE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		case 22: //  "PRE_GA_DELETE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		case 23: //  "WRITE_ROWS_EVENT_V1"

			printEventBody(t, file, eventHeader)
		case 24: //  "UPDATE_ROWS_EVENT_V1"

			printEventBody(t, file, eventHeader)
		case 25: //  "DELETE_ROWS_EVENT_V1"

			printEventBody(t, file, eventHeader)
		case 26: //  "INCIDENT_EVENT"

			printEventBody(t, file, eventHeader)
		case 27: //  "HEARTBEAT_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 28: //  "IGNORABLE_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 29: //  "ROWS_QUERY_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 30: //  "WRITE_ROWS_EVENT"
			writeRowsEvent, err := ReadWriteRowsEvent(file, eventHeader)
			if err != nil {
				t.Fatalf("%v", err)
			}
			fmt.Printf("%+v\n", writeRowsEvent)

		case 31: //  "UPDATE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		case 32: //  "DELETE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		case 33: //  "GTID_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 34: //  "ANONYMOUS_GTID_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 35: //  "PREVIOUS_GTIDS_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 36: //  "TRANSACTION_CONTEXT_EVENT"

			printEventBody(t, file, eventHeader)
		case 37: //  "VIEW_CHANGE_EVENT"

			printEventBody(t, file, eventHeader)
		case 38: //  "XA_PREPARE_LOG_EVENT"

			printEventBody(t, file, eventHeader)
		case 39: //  "PARTIAL_UPDATE_ROWS_EVENT"

			printEventBody(t, file, eventHeader)
		default:
			printEventBody(t, file, eventHeader)
		}
	}

	CloseBinlog(file)
}

func printEventBody(t *testing.T, file *os.File, eventHeader *EventHeader) {
	rawEvent, err := ReadRawEvent(file, eventHeader)
	if err != nil {
		t.Fatalf("%v", err)
	}
	fmt.Printf("Body: %X\n", rawEvent.Body)
}
