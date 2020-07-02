//go 1.10.4
package main

import (
	"fmt"
	"math"
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

type Add struct {
	E1, E2 Expression
}

type Mul struct {
	E1, E2 Expression
}

type Div struct {
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

// Converts expression to a string
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

// Simplify expressions
// Cleans up chains of Muls and Adds,
// Remove con nodes.
func Simplify(e Expression) Expression {
	// recursive descent
	var a, b Expression
	switch v := e.(type) {
	case con:
		// don't do further processing
		// just strip constant symbols
		return Simplify(v.E1)
	case Cos:
		return Cos{Simplify(v.E1)}
	case Sin:
		return Sin{Simplify(v.E1)}
	case Pow:
		return Pow{Simplify(v.Base), v.Exponent}
	case Mul:
		a = Simplify(v.E1)
		b = Simplify(v.E2)
		e = Mul{a, b}
	case Add:
		a = Simplify(v.E1)
		b = Simplify(v.E2)
		e = Add{a, b}
	}

	// Clean up chains of Adds
	if _, ok := e.(Add); ok {
		var toCheck []Expression
		// check left branch
		switch v := a.(type) {
		case Add:
			toCheck = append(toCheck, v.E1)
			toCheck = append(toCheck, v.E2)
		default:
			toCheck = append(toCheck, a)
		}
		// check right branch
		switch v := b.(type) {
		case Add:
			toCheck = append(toCheck, v.E1)
			toCheck = append(toCheck, v.E2)
		default:
			toCheck = append(toCheck, b)
		}

		// Start Summing
		sum := 0.0
		var sumlist []Expression
		for _, elt := range toCheck {
			if n, ok := elt.(Num); ok {
				sum += n.Val
				continue
			}
			sumlist = append(sumlist, elt)
		}

		switch {
		case almostEqual(sum, 0):
			// pass
			if len(sumlist) == 0 {
				return Num{0.}
			}
		default:
			sumlist = append([]Expression{Num{sum}}, sumlist...)
		}
		//debug

		//readjust summands
		// z is the end of the list
		z := sumlist[len(sumlist)-1]
		for i := len(sumlist) - 2; i >= 0; i-- {
			z = Add{sumlist[i], z}
		}
		return z

	}

	// Clean up chains of Muls
	// if it's a mul, collect branches
	if _, ok := e.(Mul); ok {
		var toCheck []Expression
		// check left branch
		switch v := a.(type) {
		case Mul:
			toCheck = append(toCheck, v.E1)
			toCheck = append(toCheck, v.E2)
		case con:
			panic("left con")
		default:
			toCheck = append(toCheck, a)
		}
		// check right branch
		switch v := b.(type) {
		case Mul:
			toCheck = append(toCheck, v.E1)
			toCheck = append(toCheck, v.E2)
		case con:
			panic("right con")
		default:
			toCheck = append(toCheck, b)
		}

		// multiply actual numbers
		// put coefficient on leftmost bramch
		co := 1.0
		var mlist []Expression
		for _, elt := range toCheck {
			if n, ok := elt.(Num); ok {
				co *= n.Val
				continue
			}
			mlist = append(mlist, elt)
		}

		switch {
		case almostEqual(co, 1.0):
		case almostEqual(co, 0.0):
			mlist = []Expression{Num{0.}}
		default:
			mlist = append([]Expression{Num{co}}, mlist...)
		}

		//readjust multiplicands
		z := mlist[len(mlist)-1]
		for i := len(mlist) - 2; i >= 0; i-- {
			z = Mul{mlist[i], z}
		}
		return z
	}

	return e
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
		c := markTreesConstant(va, v.Base)
		if checkCon(c) {
			return con{Pow{c, v.Exponent}}
		}
		return Pow{c, v.Exponent}
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

func almostEqual(a, b float64) bool {
	return math.Abs(a-b) < .00000001
}

func main() {
	if !cycleTest() {
		fmt.Println("Cycle tests passed without error.")
	}
	if !testDerive() {
		fmt.Println("Derive tests passed without error.")
	}
	if !testPartialDerive() {
		fmt.Println("Partial Derivative tests passed without error.")
	}
	if !testSimplify() {
		fmt.Println("Simplify tests passed without error.")
	}
}

/*
* TESTS
* To be moved to test file post-prototype
 */

func cycleTest() bool {
	var t Expression = Sin{Var{"x"}}
	table := []string{
		"Sin(x)",
		"Cos(x)",
		"(-1*Sin(x))",
		"(-1*Cos(x))",
		"Sin(x)",
		"Cos(x)",
		"(-1*Sin(x))",
	}
	failure := false
	for _, elt := range table {
		if Read(t) != elt {
			fmt.Printf("Trig cycle test failure. Want %v, got %v", elt, Read(t))
			failure = true
		}
		t = Derive(t)
	}
	return failure
}

// Test Derive
func testDerive() bool {
	table := []struct {
		description string
		function    Expression
		derivative  Expression
	}{
		{"sin(6 * sin(x))",
			Sin{Mul{Num{6.0}, Sin{Var{"x"}}}},
			Mul{
				Num{6.0},
				Mul{
					Cos{Mul{Num{6.0}, Sin{Var{"x"}}}},
					Cos{Var{"x"}},
				},
			},
		},

		{"x^4 + 3x^9",
			Add{Pow{Var{"x"}, 4.},
				Mul{Num{3.}, Pow{Var{"x"}, 9.}}},
			Add{Mul{Num{4.}, Pow{Var{"x"}, 3.}},
				Mul{Num{27.}, Pow{Var{"x"}, 8.}}},
		},
	}
	failure := false
	for _, tt := range table {
		raw := Derive(tt.function)
		d := Simplify(raw) // test it simplified
		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("Error. Raw:\n %v\n Got:\n %v, want:\n %v \n", Read(raw), Read(d), Read(tt.derivative))
			failure = true
		}
	}
	return failure
}

// Test table for partial derive
func testPartialDerive() bool {
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
		{"sin(x*y)",
			Var{"x"},
			Sin{Mul{Var{"x"}, Var{"y"}}},
			Mul{
				Cos{Mul{Var{"x"}, Var{"y"}}},
				Var{"y"},
			},
		},
		{"5*cos(y *x)^3",
			Var{"x"},
			Mul{Num{5.0}, Pow{Cos{Mul{Var{"x"}, Var{"y"}}}, 3.}},
			Mul{
				Num{-15.},
				Mul{
					Pow{Cos{Mul{Var{"x"}, Var{"y"}}}, 2.},
					Mul{Sin{Mul{Var{"x"}, Var{"y"}}}, Var{"y"}},
				},
			},
		},
	}
	failure := false
	for _, tt := range table {
		raw := PartialDerive(tt.variable, tt.function)
		d := Simplify(raw)

		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("\nPartialDerive Error %v wrt %v\n",
				tt.description, tt.variable)
			fmt.Printf("\nPresimplified output: %v\n",
				Read(raw))
			fmt.Printf("got  %v\nwant %v\n",
				Read(d),
				Read(tt.derivative),
			)
			failure = true
		}
	}
	return failure
}

func testSimplify() bool {
	table := []struct {
		description string
		f           Expression
		simplified  Expression
	}{
		{"5*((3*z)*(y*-1))",
			Mul{Num{5.}, Mul{Mul{Num{3.}, Var{"z"}}, Mul{Var{"y"}, Num{-1.}}}},
			Mul{Num{-15.}, Mul{Var{"z"}, Var{"y"}}},
		},
		{"5+ (6*cos(x) * 0)",
			Add{Num{5.}, Mul{Num{6.}, Mul{Cos{Var{"x"}}, Num{0.}}}},
			Num{5.},
		},
		{"con(c + 2)",
			con{Add{Var{"c"}, Num{2.}}},
			Add{Num{2.}, Var{"c"}},
		},
		{"Cos (x * con(y))",
			Cos{Mul{Var{"x"}, con{Var{"y"}}}},
			Cos{Mul{Var{"x"}, Var{"y"}}},
		},
		{"((3*-1)*(100*10))",
			Mul{Mul{Num{3.}, Num{-1.}}, Mul{Num{100.}, Num{10.}}},
			Num{-3000.},
		},
	}
	failure := false
	for _, tt := range table {
		if got := Simplify(tt.f); !reflect.DeepEqual(got, tt.simplified) {
			fmt.Printf("\nSimplify Error %v\n", tt.description)
			fmt.Printf("got  %v\nwant %v\n",
				Read(got),
				Read(tt.simplified),
			)
			failure = true
		}
	}
	return failure
}
