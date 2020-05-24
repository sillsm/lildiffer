//go 1.10.4

package main

import (
	"fmt"
	"reflect"
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

// package internal struct for
// marking subtrees constant
type con struct {
	E1 Expression
}

// mark all subtrees that don't involve
// the variable as constant
func markTreesConstant(va Var, e Expression) Expression {
	checkCon := func(exp Expression) bool {
		if _, ok := exp.(con); ok {
			return true
		}
		return false
	}
	switch v := e.(type) {
	case Num:
		return con{v}
	case Var:
		if !reflect.DeepEqual(va, v) {
			return con{v}
		}
		return v
	case Cos:
		c := markTreesConstant(va, v.E1)
		if checkCon(c) {
			return con{Cos{c}}
		}
		return Cos{c}
	case Sin:
		c := markTreesConstant(va, v.E1)
		if checkCon(c) {
			return con{Sin{c}}
		}
		return Sin{c}
	case Pow:
		return v
	case Mul:
		a := markTreesConstant(va, v.E1)
		b := markTreesConstant(va, v.E2)
		if checkCon(a) && checkCon(b) {
			return con{Mul{a, b}}
		}
		return Mul{a, b}
	case Add:
		// if either summand not constant
		// then add isn't constant
		a := markTreesConstant(va, v.E1)
		b := markTreesConstant(va, v.E2)
		if checkCon(a) && checkCon(b) {
			return con{Add{a, b}}
		}
		return Add{a, b}
	default:
		fmt.Printf("default")
		return v
	}
}

// Partial differentiation is normal
// differentiation, but first you mark
// all sub-expressions that don't involve
// the variable you're differentiating
// with respect to as constant
func PartialDerive(va Var, e Expression) Expression {
	return Derive(markTreesConstant(va, e))
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
		case con:
			return Num{0.}
		}
		// panic("undefined derivative")
		return exp
	}

	// chain rule and product rule
	switch v := e.(type) {
	case con:
		return derive(v)
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
func Read(e Expression) string {
	e = Simplify(e)
	switch v := e.(type) {
	case Cos:
		return fmt.Sprintf("Cos(%v)", Read(v.E1))
	case Sin:
		return fmt.Sprintf("Sin(%v)", Read(v.E1))
	case Mul:
		return fmt.Sprintf("(%v*%v)",
			Read(v.E1), Read(v.E2))
	case Add:
		return fmt.Sprintf("(%v+%v)",
			Read(v.E1), Read(v.E2))
	case Pow:
		return fmt.Sprintf("%v^%v",
			Read(v.Base), v.Exponent)
	case Num:
		return fmt.Sprintf("%v", v.Val)
	case Var:
		return fmt.Sprintf("%v", v.Name)
	case con:
		return fmt.Sprintf("CONST(%v)", Read(v.E1))
	}
	return ""
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
	// Remove all constant expressions
	case con:
		return Simplify(v.E1)
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
		t = Simplify(t)
		fmt.Printf("%v\n", Read(t))
		t = Derive(t)
	}

}

// Test table for Derive
func testTable() {
	table := []struct {
		description string
		function    Expression
		derivative  Expression
	}{
		{"sin(6 * sin(x))",
			Sin{Mul{Num{6.0}, Sin{Var{"x"}}}},
			Mul{
				Cos{Mul{Num{6.0}, Sin{Var{"x"}}}},
				Mul{Num{6.0}, Cos{Var{"x"}}},
			}},
		{"x^4 + 3x^9",
			Add{Pow{Var{"x"}, 4.},
				Mul{Num{3.}, Pow{Var{"x"}, 9.}}},
			Add{Mul{Num{4.}, Pow{Var{"x"}, 3.}},
				Mul{Num{27.}, Pow{Var{"x"}, 8.}}},
		},
	}

	for _, tt := range table {
		d := Simplify(Simplify(Derive(tt.function)))
		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("Error. Got %v, want %v \n", d, tt.derivative)
			Read(d)
			fmt.Printf("NEW\n")
			Read(tt.derivative)
			fmt.Printf("NEW\n")
		}
	}
}

// Test table for partial derive
func testPartialDerive() {
	table := []struct {
		description string
		variable    Var
		function    Expression
		derivative  Expression
	}{
		{"a * sin(5+b))",
			Var{"a"},
			Mul{Var{"a"}, Sin{Add{Num{5.}, Var{"b"}}}},
			Sin{Add{Num{5.}, Var{"b"}}},
		},
		{"a * sin(5+b))",
			Var{"b"},
			Mul{Var{"a"}, Sin{Add{Num{5.}, Var{"b"}}}},
			Mul{Var{"a"}, Cos{Add{Num{5.}, Var{"b"}}}},
		},
		{"sin(x * sin(5+y))",
			Var{"x"},
			Sin{Mul{Var{"x"}, Sin{Add{Num{5.}, Var{"y"}}}}},
			Mul{
				Cos{Mul{Var{"x"}, Sin{Add{Num{5.}, Var{"y"}}}}},
				Sin{Add{Num{5.}, Var{"y"}}},
			},
		},
	}

	for _, tt := range table {
		p := PartialDerive(tt.variable, tt.function)
		d := Simplify(Simplify(p))

		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("\nPartialDerive Error %v wrt %v\n",
				tt.description, tt.variable)
			fmt.Printf("got  %v\nwant %v\n",
				Read(d),
				Read(tt.derivative),
			)
		}
	}
}

func main() {
	cycleTest()
	a := Add{Sin{Var{"y"}}, Cos{Var{"x"}}}
	Read(a)
	b := Derive(a)
	Read(b)
	fmt.Printf("\n")
	testTable()
	testPartialDerive()
}
