/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Normalize
public import DixmierFormal.Scalar.AppendixA3Coefficients

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- Translate the normalized Appendix A.3 companion equation into the exact
polynomial factor equation consumed by the residual and coefficient lemmas. -/
theorem appendix_A3_normalized_factor_equation {ρ s : ℕ} {A B : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1) (hB0 : B.eval 0 = 1)
    (hAdeg : A.natDegree = 2) (hBdeg : B.natDegree = 3)
    (hu : A.coeff 1 = 1)
    (hcomp : Comp ρ s (A*B^2) (A*B*(-1))) :
    let h := ρ-2*s;
    -X*(C (h : ℂ)*(1+C (1:ℂ)*X+C (A.coeff 2)*X^2)*
        derivative (1+C (B.coeff 1)*X+C (B.coeff 2)*X^2+C (B.coeff 3)*X^3)
      -C (s : ℂ)*derivative (1+C (1:ℂ)*X+C (A.coeff 2)*X^2)*
        (1+C (B.coeff 1)*X+C (B.coeff 2)*X^2+C (B.coeff 3)*X^3))
      +(1+C (1:ℂ)*X+C (A.coeff 2)*X^2)*
        (1+C (B.coeff 1)*X+C (B.coeff 2)*X^2+C (B.coeff 3)*X^3)-1=0 := by
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hA0
    norm_num at hA0
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hCE : CompanionEq (ρ : ℤ) (s : ℤ) (A*B^2) (A*B*(-1)) :=
    (companionEq_natCast_iff ρ s (A*B^2) (A*B*(-1))).mpr hcomp
  have hgt := appendix_A3_h_gt_one hsρ hA0 hB0 (by norm_num : Polynomial.eval 0 (-1 : ℂ[X]) = -1)
    hAdeg hBdeg (by norm_num : (-1 : ℂ[X]).natDegree = 0) hcomp
  have hfactor := factor_equation_of_companion (ρ : ℤ) (s : ℤ) A B (-1) hA hB hCE
  let h : ℕ := ρ-2*s
  have hh : (ρ : ℂ)-2*(s : ℂ) = (h : ℂ) := by
    dsimp [h]
    rw [Nat.cast_sub (by omega : 2*s ≤ ρ)]
    push_cast
    ring
  have hh' : ((ρ : ℤ) : ℂ)-2*((s : ℤ) : ℂ) = (h : ℂ) := by
    simpa using hh
  have hpoly : -X*(C (h : ℂ)*A*derivative B-C (s : ℂ)*derivative A*B)+A*B-1=0 := by
    rw [hh'] at hfactor
    norm_num [derivative_neg, derivative_one] at hfactor
    simp only [map_natCast]
    linear_combination hfactor
  have hAexp := appendix_A3_quadratic_expansion hAdeg hA0
  have hBexp := appendix_A3_cubic_expansion hBdeg hB0
  rw [hAexp,hBexp,hu] at hpoly
  dsimp
  exact hpoly

end Dixmier
