module

public import Mathlib.Algebra.MvPolynomial.Basic

public section

/-- Exponent-first coefficient syntax for fully applied projections. -/
macro "MvPolynomial.coeff" e:term:max p:term:max : term =>
  `(AddMonoidAlgebra.coeff $p $e)

/-- Exponent-first partial application for coefficient linear functionals. -/
macro "MvPolynomial.coeff" e:term:max : term =>
  `(fun p => AddMonoidAlgebra.coeff p $e)
