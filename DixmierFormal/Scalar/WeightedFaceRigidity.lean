/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Companion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Rigidity of a weighted face-Jacobian identity

The crossing-face calculation reduces the Poisson bracket of faces of the form
`Y * A(X^d Y^ell)` and `X * B(X^d Y^ell)` to a weighted Euler expression in `A` and `B`.
This file proves that such an expression can be constant only when both factors are constant.
-/

namespace Dixmier

open Polynomial

/-- A constant weighted Euler-Jacobian expression has no positive-degree factors.

This is the univariate rigidity step for a crossing pair of weighted faces. The natural-number
weights are essential: the top coefficient is multiplied by `1 + d * deg B + ell * deg A`,
which is a positive integer. -/
theorem weightedFaceEuler_eq_constant_forces_degree_zero
    {A B : ℂ[X]} {d ell c : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h : A * B + C (d : ℂ) * A * euler B + C (ell : ℂ) * euler A * B = C (c : ℂ)) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  let m := A.natDegree
  let n := B.natDegree
  have htopA : A.coeff m ≠ 0 := by
    rw [show m = A.natDegree by rfl, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hA
  have htopB : B.coeff n ≠ 0 := by
    rw [show n = B.natDegree by rfl, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hB
  by_contra hdegree
  have hdegree' : ¬ (m = 0 ∧ n = 0) := by
    simpa [m, n] using hdegree
  have hmpos : 0 < m + n := by omega
  have hAB : (A * B).coeff (m + n) = A.coeff m * B.coeff n :=
    coeff_mul_of_natDegree_le' le_rfl le_rfl
  have hAeB : (C (d : ℂ) * A * euler B).coeff (m + n) =
      (d : ℂ) * A.coeff m * ((n : ℂ) * B.coeff n) := by
    calc
      (C (d : ℂ) * A * euler B).coeff (m + n) =
          (C (d : ℂ) * A).coeff m * (euler B).coeff n :=
        coeff_mul_of_natDegree_le'
          (natDegree_C_mul_le _ _)
          (natDegree_euler_le B)
      _ = (d : ℂ) * A.coeff m * ((n : ℂ) * B.coeff n) := by
        rw [coeff_C_mul, coeff_euler]
  have heAB : (C (ell : ℂ) * euler A * B).coeff (m + n) =
      (ell : ℂ) * ((m : ℂ) * A.coeff m) * B.coeff n := by
    calc
      (C (ell : ℂ) * euler A * B).coeff (m + n) =
          (C (ell : ℂ) * euler A).coeff m * B.coeff n :=
        coeff_mul_of_natDegree_le'
          ((natDegree_C_mul_le _ _).trans (natDegree_euler_le A))
          le_rfl
      _ = (ell : ℂ) * ((m : ℂ) * A.coeff m) * B.coeff n := by
        rw [coeff_C_mul, coeff_euler]
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (m + n)) h
  simp only [coeff_add, hAB, hAeB, heAB, coeff_C] at hcoeff
  simp only [if_neg (Nat.ne_of_gt hmpos)] at hcoeff
  have htop :
      ((1 : ℂ) + (d : ℂ) * (n : ℂ) + (ell : ℂ) * (m : ℂ)) *
          A.coeff m * B.coeff n = 0 := by
    linear_combination hcoeff
  have hscalar :
      (1 : ℂ) + (d : ℂ) * (n : ℂ) + (ell : ℂ) * (m : ℂ) ≠ 0 := by
    have hnat : 0 < 1 + d * n + ell * m := by omega
    have hcast : ((1 + d * n + ell * m : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnat)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hcast
  have hprod :
      ((1 : ℂ) + (d : ℂ) * (n : ℂ) + (ell : ℂ) * (m : ℂ)) *
          A.coeff m * B.coeff n ≠ 0 :=
    mul_ne_zero (mul_ne_zero hscalar htopA) htopB
  exact False.elim (hprod htop)

end Dixmier
