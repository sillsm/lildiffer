//go 1.10.4
package main

import (
	"fmt"
	"math"
	"reflect"
	"regexp"
	"sort"
	"strconv"
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

// polynomial type
type Poly struct {
	//terms and coefficients map
	terms map[string]float64
}

// Simplify monomial products
// e.g xxy^2zx - > x^3y^2z
func reduce(s string) string {
	if len(s) == 0 {
		return ""
	}

	var monomials []string
	var exponents []int

	re := regexp.MustCompile(`[a-z]\^[0-9\-]+`)

	// Pack monomials and exponents with the single cases
	for _, r := range re.ReplaceAllString(s, "") {
		monomials = append(monomials, string(r))
		exponents = append(exponents, 1)
	}

	// Parse and pack the monomials with non-1 exponents
	for _, str := range re.FindAllString(s, -1) {
		monomials = append(monomials, string(str[0]))
		i, err := strconv.Atoi(str[2:])
		if err != nil {
			panic(err)
		}
		exponents = append(exponents, i)
	}

	// Now get rid of repeats, multiply
	m := make(map[string]int)
	for i, st := range monomials {
		if val, ok := m[st]; ok {
			m[st] = val + exponents[i]
		} else {
			m[st] = exponents[i]
		}
	}

	// Make reduced term
	var ret string
	var sorted []string
	for key := range m {
		sorted = append(sorted, key)
	}
	sort.Strings(sorted)
	for _, key := range sorted {
		v := m[key]
		switch v {
		case 1:
			ret += key
		default:
			ret += fmt.Sprintf("%v^%v", key, v)
		}
	}
	return ret
}

func newPoly(m map[string]float64) Poly {
	r := make(map[string]float64)
	for key, value := range m {
		key = reduce(key)
		if _, ok := r[key]; ok {
			panic("polynomial init error")
		}
		r[key] = value
	}
	return Poly{r}
}

func almostEqual(a, b float64) bool {
	return math.Abs(a-b) < .0000000001
}

func mul(p1, p2 Poly) Poly {
	r := make(map[string]float64)
	for k1, v1 := range p1.terms {
		for k2, v2 := range p2.terms {
			key := reduce(k1 + k2)
			if val, ok := r[key]; ok {
				r[key] = val + v1*v2
			} else {
				r[key] = v1 * v2
			}
			if v := r[key]; almostEqual(v, 0.) {
				delete(r, key)
			}
		}
	}
	return Poly{r}
}

// combine like terms
func add(p1, p2 Poly) Poly {
	for key, value := range p1.terms {
		if _, ok := p2.terms[key]; ok {
			//there's a like term
			p2.terms[key] = p2.terms[key] + value
		} else {
			p2.terms[key] = value
		}
		if v := p2.terms[key]; almostEqual(v, 0.) {
			delete(p2.terms, key)
		}
	}
	return p2
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
	case Div:
		return fmt.Sprintf("(%v/%v)",
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
	case Poly:
		return fmt.Sprintf("P{%v}", v.terms)
	}
	return ""
}

// Bunch of techniques to simplify expression trees.
func Simplify(e Expression) Expression {
	return simplify(e)
}

// makePoly attempts to rearrange expression terms as polynomials
func makePoly(e Expression) Expression {
	// Given an expression, try making a poly out of it
	tryPoly := func(e Expression) Expression {
		switch v := e.(type) {
		case Var:
			return newPoly(map[string]float64{v.Name: 1.})
		case Num:
			return newPoly(map[string]float64{"": v.Val})
		}
		return e
	}
	tryPoly = tryPoly

	var a, b Expression
	switch v := e.(type) {
	case con:
		// don't do further processing
		// just strip constant symbols
		return makePoly(v.E1)
	case Cos:
		return Cos{makePoly(v.E1)}
	case Sin:
		return Sin{makePoly(v.E1)}
	case Pow:
		return Pow{makePoly(v.Base), v.Exponent}
	case Div:
		return Div{makePoly(v.E1), makePoly(v.E2)}
	case Num:
		return tryPoly(v)
	case Var:
		return tryPoly(v)
	case Poly:
		return v
	case Mul:
		a = tryPoly(makePoly(v.E1))
		b = tryPoly(makePoly(v.E2))
	case Add:
		a = tryPoly(makePoly(v.E1))
		b = tryPoly(makePoly(v.E2))
	}

	_, ok1 := a.(Poly)
	_, ok2 := b.(Poly)

	switch e.(type) {
	case Mul:
		if ok1 && ok2 {
			return mul(a.(Poly), b.(Poly))
		}
	case Add:
		if ok1 && ok2 {
			return add(a.(Poly), b.(Poly))
		}

	}

	return e
}

// Simplify expressions
// Cleans up chains of Muls and Adds,
// Remove con nodes.
func simplify(e Expression) Expression {
	// recursive descent
	var a, b Expression
	switch v := e.(type) {
	case con:
		// don't do further processing
		// just strip constant symbols
		return simplify(v.E1)
	case Cos:
		return Cos{simplify(v.E1)}
	case Sin:
		return Sin{simplify(v.E1)}
	case Pow:
		return Pow{simplify(v.Base), v.Exponent}
	case Div:
		return Div{simplify(v.E1), simplify(v.E2)}
	case Mul:
		a = simplify(v.E1)
		b = simplify(v.E2)
		e = Mul{a, b}
	case Add:
		a = simplify(v.E1)
		b = simplify(v.E2)
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
		// Attempt distributing a coefficient over a sum
		// Turn Mul{num, Add} into Add {num*add.v1,num*add.v2}

		switch v := z.(type) {
		case Mul:
			switch sum := v.E2.(type) {
			case Add:
				return simplify(Add{
					Mul{v.E1, sum.E1},
					Mul{v.E1, sum.E2},
				})
			}
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
	case Div:
		a := markTreesConstant(va, v.E1)
		b := markTreesConstant(va, v.E2)
		if checkCon(a) && checkCon(b) {
			return con{Div{a, b}}
		}
		return Div{a, b}
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
			// subtrees marked constant automatically have 0 as their derivative
		case con:
			return Num{0.}
		}
		// panic("undefined derivative")
		return exp
	}

	// chain rule, product rule, quotient rule
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
	// quotient rule
	case Div:
		return Div{
			Add{Mul{Derive(v.E1), v.E2}, Mul{Num{-1.}, Mul{v.E1, Derive(v.E2)}}},
			Mul{v.E2, v.E2},
		}
	case Add:
		return Add{
			Derive(v.E1),
			Derive(v.E2),
		}
	}
	fmt.Printf("Why did I get here? %v\n", e)
	panic(fmt.Sprintf("missed a case of type %v", Read(e)))
}

func g(Expression) (Expression, Expression) {
	return Var{"a"}, Var{"b"}
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
	if !polyMulTest() {
		fmt.Println("Polynomial multiplication tests passed without error.")
	}
	if !polyAddTest() {
		fmt.Println("Polynomial addition tests passed without error.")
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
	type ptype map[string]float64
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
		// https://tutorial.math.lamar.edu/classes/calci/productquotientrule.aspx
		{"(3z+9) / (2-z)",
			Div{Add{Mul{Num{3.0}, Var{"z"}}, Num{9.}},
				Add{Num{2.}, Mul{Num{-1.}, Var{"z"}}}},
			Div{newPoly(ptype{"": 15.}),
				newPoly(ptype{"": 4., "z^2": 1, "z": -4.})},
		},
	}
	failure := false
	for _, tt := range table {
		raw := Derive(tt.function)
		d := makePoly(Simplify(raw)) // test it simplified
		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("TestDerive Error. Raw:\n %v\n Got:\n %v, want:\n %v \n", Read(raw), Read(d), Read(tt.derivative))
			failure = true
		}
	}
	return failure
}

// Test table for partial derive
func testPartialDerive() bool {
	type ptype map[string]float64
	table := []struct {
		description string
		variable    Var
		function    Expression
		derivative  Expression
	}{
		{"a * sin(5+b))",
			Var{"a"},
			Mul{Var{"a"}, Sin{Add{Num{5.}, Var{"b"}}}},
			Sin{newPoly(ptype{"": 5., "b": 1})},
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
		d := makePoly(Simplify(raw))

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
	type ptype map[string]float64
	table := []struct {
		description string
		f           Expression
		simplified  Expression
	}{
		{"5*((3*z)*(y*-1))",
			Mul{Num{5.}, Mul{Mul{Num{3.}, Var{"z"}}, Mul{Var{"y"}, Num{-1.}}}},
			newPoly(ptype{"yz": -15}),
		},
		{"5+ (6*cos(x) * 0)",
			Add{Num{5.}, Mul{Num{6.}, Mul{Cos{Var{"x"}}, Num{0.}}}},
			newPoly(ptype{"": 5.}),
		},
		{"con(c + 2)",
			con{Add{Var{"c"}, Num{2.}}},
			newPoly(ptype{"": 2., "c": 1}),
		},
		{"9 + (3 x (2+ z))",
			Add{Num{9.}, Mul{Num{3.}, Add{Num{2.}, Var{"z"}}}},
			newPoly(ptype{"": 15, "z": 3}),
		},
		{"-1 * ((2+ (-1 * z)) * z)",
			Mul{Num{-1.}, Mul{Add{Num{2.0}, Mul{Num{-1.}, Var{"z"}}}, Var{"z"}}},
			newPoly(ptype{"z^2": 1, "z": -2}),
		},
		{"4.5 * (2 + y)",
			Mul{Num{4.5}, Add{Num{2.}, Var{"y"}}},
			newPoly(ptype{"y": 4.5, "": 9}),
		},

		{"Cos (x * con(y))",
			Cos{Mul{Var{"x"}, con{Var{"y"}}}},
			Cos{newPoly(ptype{"xy": 1})},
		},
		{"((3*-1)*(100*10))",
			Mul{Mul{Num{3.}, Num{-1.}}, Mul{Num{100.}, Num{10.}}},
			newPoly(ptype{"": -3000}),
		},
	}
	failure := false
	for _, tt := range table {
		if got := makePoly(Simplify(tt.f)); !reflect.DeepEqual(got, tt.simplified) {
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

/*
* Polynomial TESTS
*
 */
func polyAddTest() bool {
	type ptype map[string]float64
	table := []struct {
		p1, p2 map[string]float64
		sum    map[string]float64
	}{
		{
			ptype{"": 4., "x^2y^5": 3.5, "x": 2.},
			ptype{"x": 1.},
			ptype{"": 4, "x": 3., "x^2y^5": 3.5},
		},

		{
			ptype{"x^2y^111z^3": 1},
			ptype{"y^2nmz^2": 1},
			ptype{"x^2y^111z^3": 1, "y^2nmz^2": 1},
		},
		{
			ptype{"": 1, "x": 1},
			ptype{"": 1, "x": -1},
			ptype{"": 2},
		},
		{
			ptype{"": 1, "x": 1, "y": 1},
			ptype{"": -1, "x": 1, "y": -1},
			ptype{"x": 2},
		},
	}
	failure := false
	for _, t := range table {
		got := add(newPoly(t.p1), newPoly(t.p2))
		want := newPoly(t.sum)
		if !reflect.DeepEqual(got, want) {
			fmt.Printf(
				"Poly add Error on \n%v * %v\n want \n%v got \n%v\n\n",
				t.p1, t.p2, want, got)
			failure = true
		}

	}
	return failure
}

func polyMulTest() bool {
	type ptype map[string]float64
	table := []struct {
		p1, p2  map[string]float64
		product map[string]float64
	}{
		{
			ptype{"": 4., "x^2y^5": 3.5, "x": 2.},
			ptype{"x": 1.},
			ptype{"x": 4., "x^3y^5": 3.5, "x^2": 2.},
		},
		{
			ptype{"x^2y^111z^3": 1},
			ptype{"y^2nmz^2": 1},
			ptype{"mnx^2y^113z^5": 1},
		},
		{
			ptype{"": 1, "x": 1},
			ptype{"": 1, "x": -1},
			ptype{"": 1, "x^2": -1},
		},
		{
			ptype{"": 1, "x": 1, "y": 1},
			ptype{"": -1, "x": 1, "y": -1},
			ptype{"": -1, "x^2": 1, "y^2": -1, "y": -2.},
		},
	}
	failure := false
	for _, t := range table {
		got := mul(newPoly(t.p1), newPoly(t.p2))
		want := newPoly(t.product)
		if !reflect.DeepEqual(got, want) {
			fmt.Printf(
				"Poly Mul Error on \n%v * %v\n want \n%v got \n%v\n\n",
				t.p1, t.p2, want, got)
			failure = true
		}

	}
	return failure
}
