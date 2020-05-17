//go 1.10.4

package main

import (
	"fmt"
)

// An Expr is a struct which implements Derive
// usually an nary expression tree
type Expression interface {
}

// functions are sigil types
type Cos struct {
	E1 Expression
}

type Sin struct {
	E1 Expression
}

// todo: more generalized exponents
type Pow struct {
	Base     Expression
	Exponent float64
}

type Mul struct {
	E1, E2 Expression
}

type Add struct {
	E1, E2 Expression
}

type Num struct {
	Val float64
}

type Var struct {
	Name string
}

// derivatives are recursive rewrite rules
// for expression trees
func Derive(e Expression) Expression {
	// Derivative Table
	derive := func(exp Expression) Expression {
		switch v := exp.(type) {
		case Pow:
			return Mul{Num{v.Exponent},
				Pow{v.Base, v.Exponent - 1.}}
		case Cos:
			return Mul{Num{-1.}, Sin{v.E1}}
		case Sin:
			return Cos{v.E1}
		case Num:
			return Num{0.}
		case Var:
			return Num{1.}
			// case
		}
		// panic("undefined derivative")
		return exp
	}

	// chain rule and product rule
	switch v := e.(type) {
	case Num:
		return derive(v)
	case Var:
		return derive(v)
	case Cos:
		return Mul{derive(v), Derive(v.E1)}
	case Sin:
		return Mul{derive(v), Derive(v.E1)}
	case Pow:
		return Mul{derive(v), Derive(v.Base)}
	case Mul:
		return Add{
			Mul{
				v.E1,
				Derive(v.E2),
			},
			Mul{
				Derive(v.E1),
				v.E2,
			},
		}
	case Add:
		return Add{
			Derive(v.E1),
			Derive(v.E2),
		}
	}
	panic("missed a case")
}

// Prints expression for debugging
func Read(e Expression) {
	//
	e = Simplify(e)
	switch v := e.(type) {
	case Cos:
		fmt.Printf("Cos(")
		Read(v.E1)
		fmt.Printf(")")
	case Sin:
		fmt.Printf("Sin(")
		Read(v.E1)
		fmt.Printf(")")
	case Mul:
		fmt.Printf("(")
		Read(v.E1)
		fmt.Printf("*")
		Read(v.E2)
		fmt.Printf(")")
	case Add:
		fmt.Printf("(")
		Read(v.E1)
		fmt.Printf("+")
		Read(v.E2)
		fmt.Printf(")")
	case Pow:
		Read(v.Base)
		fmt.Printf("^%v", v.Exponent)
	case Num:
		fmt.Printf("%v", v.Val)
	case Var:
		fmt.Printf("%v", v.Name)
	}
}

// Simplify cuts mult or add by 0
// from expression trees
func Simplify(e Expression) Expression {
	// checks if e is a num that's roughly
	// equal to f
	checkFloat := func(f float64, e Expression) bool {
		sensitivity := .0000000000001
		if t, ok := e.(Num); ok {
			if t.Val > f-sensitivity &&
				t.Val < f+sensitivity {
				return true
			}
		}
		return false
	}

	// Prune all children of mult 0
	switch v := e.(type) {
	//replace with general bfs logic
	case Cos:
		return Cos{Simplify(v.E1)}
	case Sin:
		return Sin{Simplify(v.E1)}
	case Mul:
		if checkFloat(0., v.E1) {
			return Num{0.}
		}
		if checkFloat(0., v.E2) {
			return Num{0.}
		}
		if checkFloat(1., v.E2) {
			return v.E1
		}
		if checkFloat(1., v.E1) {
			return v.E2
		}
		if t1, ok1 := v.E1.(Num); ok1 {
			if t2, ok2 := v.E2.(Mul); ok2 {
				if t3, ok3 := t2.E1.(Num); ok3 {
					return Mul{
						Num{t1.Val * t3.Val},
						Simplify(t2.E2),
					}
				}
			}
		}

		return Mul{
			Simplify(v.E1),
			Simplify(v.E2),
		}
	case Add:
		if checkFloat(0., v.E1) {
			return Simplify(v.E2)
		}
		if checkFloat(0., v.E2) {
			return Simplify(v.E1)
		}

		return Add{
			Simplify(v.E1),
			Simplify(v.E2),
		}

	default:
		return v
	}
}

func cycleTest() {
	fmt.Println("\nCycle Test")
	var t Expression = Sin{Var{"x"}}
	for i := 0; i < 7; i++ {
		fmt.Println()
		t = Simplify(t)
		Read(t)
		t = Derive(t)
	}

}

func main() {
	cycleTest()
	a := Add{Sin{Var{"y"}}, Cos{Var{"x"}}}
	Read(a)
	fmt.Println()
	b := Derive(a)
	Read(b)
	fmt.Printf("\n")

	t2 := Sin{Mul{Num{6.0}, Sin{Var{"x"}}}}
	dt2 := Mul{
		Cos{Mul{Num{6.0}, Sin{Var{"x"}}}},
		Mul{Num{6.0}, Cos{Var{"x"}}},
	}
	Read(t2)
	fmt.Println()
	Read(dt2)
	fmt.Println()
	x := Derive(t2)
	Read(x)
	x = Derive(Mul{Num{6.}, Sin{Var{"x"}}})
	fmt.Println()
	Read(x)
	fmt.Println("\n\npolynomial")
	x = Add{Pow{Var{"x"}, 4.},
		Mul{Num{3.}, Pow{Var{"x"}, 9.}}}
	Read(x)
	fmt.Println()
	Read(Derive(x))

}
