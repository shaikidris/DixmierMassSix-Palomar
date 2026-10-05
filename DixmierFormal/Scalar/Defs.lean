/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Complex.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Scalar definitions (frozen contract)

Definitions used in the statements of the scalar results of the manuscript
*The rank-one Dixmier conjecture for elements of mass at most six*:
the number of terms of a polynomial, primitive exponent support, and the
companion differential equation of a negative crossing face.

This module is part of the frozen statement contract; see `FROZEN.sha256`.
-/

namespace Dixmier

open Polynomial

/-- `termCount p` is the number of nonzero monomials of `p` (written `t(p)` in the paper). -/
def termCount {R : Type*} [Semiring R] (p : R[X]) : ℕ := p.support.card

/-- A polynomial has *primitive exponent support* if its constant coefficient is nonzero and
the greatest common divisor of its positive exponents is one. -/
def HasPrimitiveSupport {R : Type*} [Semiring R] (p : R[X]) : Prop :=
  p.coeff 0 ≠ 0 ∧ (p.support.erase 0).gcd id = 1

/-- The companion equation of a negative crossing face,
`(ρ - s) w f r' - (f + ρ w f' + 1) r = 0` (equation (1.1) of the paper). -/
def CompanionEq (ρ s : ℤ) (r f : ℂ[X]) : Prop :=
  C ((ρ : ℂ) - (s : ℂ)) * X * f * derivative r - (f + C (ρ : ℂ) * X * derivative f + 1) * r = 0

end Dixmier
