// 示例: 结构类型的使用
package main

import (
	"log"
	"time"
)

/****************************************************************************
* 简单使用
****************************************************************************/

type Employee struct {
	ID        int
	Name      string
	Address   string
	DoB       time.Time
	Position  string
	Salary    int
	ManagerID int
}

// 返回值类型: 结构指针
func EmployeeByID(id int) *Employee {
	// 硬编码
	if id == 1 {
		return &Employee{
			ID:        1,
			Name:      "dilbert",
			Address:   "JiangSu",
			DoB:       time.Date(2001, time.September, 9, 12, 0, 0, 0, time.UTC),
			Position:  "Manager",
			Salary:    10000,
			ManagerID: 0,
		}
	} else {
		return nil
	}
}

// 返回值类型: 结构
func EmployeeByID2(id int) Employee {
	var employee = EmployeeByID(id)
	return *employee
}

/****************************************************************************
* 自引用
****************************************************************************/

// 二叉树节点: 引用自身的结构定义
type tree struct {
	value       int
	left, right *tree // 字段类型不可以是tree, 只可以是*tree
}

// Sort使用结构tree的排序方法
func Sort(values []int) {
	var root *tree
	for _, v := range values {
		root = add(root, v)
	}
	appendValues(values[:0], root)
}

// appendValues将t中元素按序添加到values中, 返回结果slice
func appendValues(values []int, t *tree) []int {
	if t != nil {
		values = appendValues(values, t.left)  // left
		values = append(values, t.value)       // this
		values = appendValues(values, t.right) // right
	}
	return values
}

// add将值value添加到树t中, 返回t
func add(t *tree, value int) *tree {
	if t == nil {
		// t = new(tree)
		// t.value = value
		// 等价于:
		t = &tree{value: value} // 便捷记法: 创建和初始化一个结构变量, 并返回其地址
		return t
	}

	if value < t.value {
		t.left = add(t.left, value) // add to left
	} else {
		t.right = add(t.right, value)
	}

	return t
}

/****************************************************************************
* 结构字面量
****************************************************************************/

type Point struct {
	X, Y int
}

// Scale: 结构作为传递参数和返回值
func Scale(p Point, factor int) Point {
	return Point{p.X * factor, p.Y * factor}
}

// Bonus: 奖金; 传递结构指针
func Bonus(e *Employee, percent int) int {
	return e.Salary * 105 / 100
}

// AwardAnnualRaise: 奖励年度加薪; 传递结构指针, 修改字段值
func AwardAnnualRaise(e *Employee) {
	e.Salary = e.Salary * 105 / 100
}

/****************************************************************************
* 结构内嵌
****************************************************************************/

type Circle struct {
	Point  // 匿名字段
	Radius int
}

type Wheel struct {
	Circle // 匿名字段
	Spokes int
}

/****************************************************************************
* 测试
****************************************************************************/

func init() {
	// log.SetFlags(log.Ldate | log.Ltime | log.Llongfile)
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
}

func main() {
	// 访问字段
	var dilbert Employee
	dilbert.ManagerID = 1
	dilbert.Salary -= 5000 // demoted
	// 通过字段的指针访问
	position := &dilbert.Position
	*position = "Senior " + *position // promoted
	// 结构的指针
	var employeeOfTheMonth *Employee = &dilbert
	employeeOfTheMonth.Position += " (proactive team player)"
	// 上面的语句等价于:
	(*employeeOfTheMonth).Position += " (proactive team player)"

	log.Printf(EmployeeByID(dilbert.ManagerID).Position)
	EmployeeByID(1).Salary = 0
	// EmployeeByID2(1).Salary = 0 // ERROR: 不能标识一个变量

	log.Printf("dilbert=%#v", dilbert)
	log.Printf("employeeOfTheMonth=%#v", *employeeOfTheMonth)

	// 测试Sort
	s := []int{9, 5, 7, 3, 4, 1}
	Sort(s)
	log.Printf("s=%v", s)

	// 空结构类型: struct{}
	log.Printf("empty struct: %#v", struct{}{})

	// 比较结构
	p := Point{1, 2}
	q := Point{2, 1}
	log.Printf("%t", p.X == q.X && p.Y == q.Y)
	log.Printf("%t", p == q)
	// 结构作为哈希表的键
	type address struct { // 临时结构定义
		hostname string
		port     int
	}
	hits := make(map[address]int)
	hits[address{"golang.org", 443}]++
	log.Printf("%#v", hits)

	// 结构内嵌
	var w Wheel
	w.X = 8 // 等价于:
	w.Circle.Point.X = 8
	w.Y = 8
	w.Radius = 5 // 等价于
	w.Circle.Radius = 5
	w.Spokes = 20
	log.Printf("w=%#v", w)
	// 结构内嵌与结构字面量: 匿名字段由隐式的名称
	w = Wheel{
		Circle: Circle{
			Point:  Point{X: 8, Y: 8},
			Radius: 5,
		},
		Spokes: 20,
	}
	log.Printf("w=%#v", w)
}
