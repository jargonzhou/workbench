package reflections

import (
	"strings"
	"testing"
	"time"
)

func TestPrintMethod(t *testing.T) {
	PrintMethod(time.Hour)
	PrintMethod(new(strings.Replacer))
}
