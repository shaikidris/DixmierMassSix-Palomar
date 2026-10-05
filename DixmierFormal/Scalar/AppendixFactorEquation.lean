/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Appendix A factor equation

This proves the differential-polynomial identity of Proposition A.1 whenever
the factorization `r = A B²`, `f = A B C` is supplied. The existence and
squarefreeness of those factors, positivity of `ρ - 2s`, and the degree
identity remain separate obligations.
-/

namespace Dixmier
open Polynomial

private theorem factor_identity (R S : ℂ) (A B Cc : ℂ[X]) :
    C (R-S) * X * (A*B*Cc) * derivative (A*B^2) -
      ((A*B*Cc) + C R * X * derivative (A*B*Cc) + 1) * (A*B^2) =
      (A*B^2) * (X*Cc*(C (R-2*S)*A*derivative B - C S*derivative A*B) -
        A*B*(C R*X*derivative Cc+Cc) - 1) := by
  rw [derivative_mul, derivative_mul, derivative_mul, derivative_pow]
  simp only [map_sub, map_mul, map_ofNat]
  have hC2 : (C (2 : ℂ) : ℂ[X]) = 2 := C_ofNat 2
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at *
  simp only [hC2]
  ring

/-- The factor equation in Proposition A.1 follows from the scalar companion
equation for any nonzero factors `A` and `B`. -/
theorem factor_equation_of_companion (ρ s : ℤ) (A B Cc : ℂ[X])
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h : CompanionEq ρ s (A*B^2) (A*B*Cc)) :
    X*Cc*(C ((ρ : ℂ)-2*(s : ℂ))*A*derivative B - C (s : ℂ)*derivative A*B) -
      A*B*(C (ρ : ℂ)*X*derivative Cc+Cc) = 1 := by
  rw [CompanionEq, factor_identity] at h
  have hAB : A * B^2 ≠ 0 := mul_ne_zero hA (pow_ne_zero _ hB)
  have hh : X*Cc*(C ((ρ : ℂ)-2*(s : ℂ))*A*derivative B -
      C (s : ℂ)*derivative A*B) - A*B*(C (ρ : ℂ)*X*derivative Cc+Cc) - 1 = 0 :=
    (mul_eq_zero.mp h).resolve_left hAB
  exact sub_eq_zero.mp hh

end Dixmier
