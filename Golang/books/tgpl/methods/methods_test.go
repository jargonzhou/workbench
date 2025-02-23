package methods

import (
	"testing"
)

func testDistance(t *testing.T) {
	p := Point{1, 2}
	q := Point{4, 6}
	t.Log(p.Distance(q))

	path := Path{
		Point{1, 1},
		Point{5, 1},
		Point{5, 4},
		Point{1, 1},
	}
	t.Log(path.Distance())
}

func testReceiver(t *testing.T) {
	p := Point{1, 2}
	pptr := &Point{1, 2}
	t.Logf("%T, %T\n", p, pptr)
	t.Log(p, *pptr)

	// type receiver
	t.Log(p.Distance(p))
	t.Log(pptr.Distance(p)) // ptr => *ptr

	// point type receiver
	pptr.ScaleBy(2.0)
	t.Log(*pptr)
	p.ScaleBy(2.0) // p => &p; 变量
	t.Log(p)
}

func TestMethodValue(t *testing.T) {
	p := Point{1, 2}
	q := Point{4, 6}

	distanceFromP := p.Distance // 方法值
	t.Log(distanceFromP(q))
}

func TestMethodExpression(t *testing.T) {
	p := Point{1, 2}
	q := Point{4, 6}

	distance := Point.Distance // 方法表达式
	t.Log(distance(p, q))
}
