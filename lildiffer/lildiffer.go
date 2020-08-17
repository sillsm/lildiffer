//go 1.10.4
package lildiffer

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
