package lildiffer

import (
  "testing"
  "reflect"
  "fmt"
)

// Ensure cyclic property of repeated derivatives
// of sine.
func TestCyclesBehavior(t *testing.T) {
	var e Expression = Sin{Var{"x"}}
	table := []string{
		"Sin(x)",
		"Cos(x)",
		"(-1*Sin(x))",
		"(-1*Cos(x))",
		"Sin(x)",
		"Cos(x)",
		"(-1*Sin(x))",
	}
	for _, elt := range table {
		if Read(e) != elt {
			t.Errorf("Trig cycle test failure. Want %v, got %v", elt, Read(e))
		}
		e = Derive(e)
	}
}

// Test Derive
func TestDerive(t *testing.T){
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
	for _, tt := range table {
		raw := Derive(tt.function)
		d := makePoly(Simplify(raw)) // test it simplified
		if !reflect.DeepEqual(d, tt.derivative) {
			fmt.Printf("TestDerive Error. Raw:\n %v\n Got:\n %v, want:\n %v \n", Read(raw), Read(d), Read(tt.derivative))
		}
	}
}

func TestPartialDerive(t *testing.T) {
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
	
	for _, tt := range table {
		raw := PartialDerive(tt.variable, tt.function)
		d := makePoly(Simplify(raw))

		if !reflect.DeepEqual(d, tt.derivative) {
			t.Errorf("\nPartialDerive Error %v wrt %v\n",
				tt.description, tt.variable)
			t.Errorf("\nPresimplified output: %v\n",
				Read(raw))
			t.Errorf("got  %v\nwant %v\n",
				Read(d),
				Read(tt.derivative),
			)
		}
	}
}


func TestSimplify(t *testing.T) {
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
	
	for _, tt := range table {
		if got := makePoly(Simplify(tt.f)); !reflect.DeepEqual(got, tt.simplified) {
			t.Errorf("\nSimplify Error %v\n", tt.description)
			t.Errorf("got  %v\nwant %v\n",
				Read(got),
				Read(tt.simplified),
			)
		}
	}
}

/*
* Polynomial TESTS
*/
 
func TestPolyAdd(t *testing.T) {
	type ptype map[string]float64
	table := []struct {
		p1, p2 map[string]float64
		sum    map[string]float64

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
	
	for _, tt := range table {
		got := add(newPoly(tt.p1), newPoly(tt.p2))
		want := newPoly(tt.sum)
		if !reflect.DeepEqual(got, want) {
			t.Errorf(
				"Poly add Error on \n%v * %v\n want \n%v got \n%v\n\n",
				tt.p1, tt.p2, want, got)
		}

	}
}

func TestPolyMul(t *testing.T){
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
	
	for _, tt := range table {
		got := mul(newPoly(tt.p1), newPoly(tt.p2))
		want := newPoly(tt.product)
		if !reflect.DeepEqual(got, want) {
			t.Errorf(
				"Poly Mul Error on \n%v * %v\n want \n%v got \n%v\n\n",
				tt.p1, tt.p2, want, got)
		}
	}
}
