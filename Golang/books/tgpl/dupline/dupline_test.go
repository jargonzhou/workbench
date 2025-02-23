package main

import (
	"testing"
)

func TestDup(t *testing.T) {
	content := `1
2
1
1
2`
	counts := make(map[string]int)
	dup(content, counts)
	t.Logf("%v", counts)
	if 3 != counts["1"] {
		t.Error(`3 != counts["1"]`)
	}
	if 2 != counts["2"] {
		t.Error(`2 != counts["2"]`)
	}
}
