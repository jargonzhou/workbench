package functions

import (
	"testing"
)

// 测试: 匿名函数
func testAnonymoudFunctions(t *testing.T) {
	sfunc := squares()
	if 1 != sfunc() {
		t.Error("should be 1")
	}
	if 4 != sfunc() {
		t.Error("should be 4")
	}
	if 9 != sfunc() {
		t.Error("should be 9")
	}
}

func testTopoSort(t *testing.T) {
	for i, course := range topoSort(prereqs) {
		t.Logf("%d:\t%s\n", i+1, course)
	}
}

func TestSum(t *testing.T) {
	t.Log(sum())
	t.Log(sum(1))
	t.Log(sum(1, 2))

	values := []int{1, 2, 3}
	t.Log(sum(values...))
}
