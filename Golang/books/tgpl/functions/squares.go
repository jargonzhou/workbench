package functions

// 返回值为函数
func squares() func() int {
	var x int // 函数值的状态
	return func() int {
		x++
		return x * x
	}
}
