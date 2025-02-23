package mysql_hack

import (
	"fmt"
	"testing"
)

func TestConstant(t *testing.T) {
	for k, v := range ColumnType {
		fmt.Printf("%d=%s\n", k, v)
	}
	fmt.Println()
	for k, v := range ColumnDefinitionFlags {
		fmt.Printf("%d=%s\n", k, v)
	}
	fmt.Println()
	for k, v := range LogEventType {
		fmt.Printf("%d=%s\n", k, v)
	}
}
