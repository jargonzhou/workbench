// 包: 表达式求值
package expr

import (
	"fmt"
	"math"
)

// 算术表达式
type Expr interface {
	// 表达式求值
	Eval(env Env) float64
}

// 变量
type Var string

// 求值环境
type Env map[Var]float64

// 数值常量
type literal float64

// 一元操作表达式
type unary struct {
	op rune // '+', '-'
	x  Expr
}

// 二元操作表达式
type binary struct {
	op   rune // '+', '-', '*', '/'
	x, y Expr
}

// 函数调用表达式
type call struct {
	fn   string // "pow", "sin", "sqrt"
	args []Expr
}

func (v Var) Eval(env Env) float64 {
	return env[v]
}

func (l literal) Eval(_ Env) float64 {
	return float64(l)
}

func (u unary) Eval(env Env) float64 {
	switch u.op {
	case '+':
		return +u.x.Eval(env)
	case '-':
		return -u.x.Eval(env)
	}
	panic(fmt.Sprintf("unsupported unary operation: %q", u.op))
}

func (b binary) Eval(env Env) float64 {
	switch b.op {
	case '+':
		return b.x.Eval(env) + b.y.Eval(env)
	case '-':
		return b.x.Eval(env) - b.y.Eval(env)
	case '*':
		return b.x.Eval(env) * b.y.Eval(env)
	case '/':
		return b.x.Eval(env) / b.y.Eval(env) // /0???
	}
	panic(fmt.Sprintf("unsupported binary operation: %q", b.op))
}

func (c call) Eval(env Env) float64 {
	// WARN: 未做校验
	switch c.fn {
	case "pow":
		return math.Pow(c.args[0].Eval(env), c.args[1].Eval(env))
	case "sin":
		return math.Sin(c.args[0].Eval(env))
	case "sqrt":
		return math.Sqrt(c.args[0].Eval(env))
	}
	panic(fmt.Sprintf("unsupported function call: %q", c.fn))
}
