package methods

import (
	"image/color"
	"math"
)

type Point struct {
	X, Y float64
}

type Path []Point

type ColoredPoint struct {
	Point
	Color color.RGBA
}

// 示例: 接收者
func (p Point) Distance(q Point) float64 {
	return math.Hypot(q.X-p.X, q.Y-p.Y)
}

func (p Path) Distance() float64 {
	sum := 0.0
	for i := range p {
		if i > 0 {
			sum += p[i-1].Distance(p[i])
		}
	}
	return sum
}

// 示例: 指针接收者
func (p *Point) ScaleBy(factor float64) {
	p.X *= factor
	p.Y *= factor
}
