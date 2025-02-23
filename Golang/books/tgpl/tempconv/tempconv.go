package tempconv

import "fmt"
import "flag"

// 数据类型定义

// 摄氏度
type Celsius float64

// 华氏度
type Fahrenheit float64

// flag
type celsiusFlag struct {
	Celsius
}

const (
	AbsoluteZeroC Celsius = -273.15
	FreezingC     Celsius = 0
	BoilingC      Celsius = 100
)

func (c Celsius) String() string {
	return fmt.Sprintf("%g°C", c)
}

func (f Fahrenheit) String() string {
	return fmt.Sprintf("%g°F", f)
}

// Set实现了flag.Value接口中方法
func (f *celsiusFlag) Set(s string) error {
	var unit string   // 单位
	var value float64 // 值
	fmt.Sscanf(s, "%f%s", &value, &unit)

	switch unit {
	case "C", "°C":
		f.Celsius = Celsius(value)
		return nil
	case "F", "°F":
		f.Celsius = FToC(Fahrenheit(value))
		return nil
	}

	return fmt.Errorf("invalid temperature %q", s)
}

// 定义flag
func CelsiusFlag(name string, value Celsius, usage string) *Celsius {
	f := celsiusFlag{value}
	flag.CommandLine.Var(&f, name, usage)
	return &f.Celsius
}
