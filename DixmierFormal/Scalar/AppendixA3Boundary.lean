/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2Power

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.3: degree relation and unit-defect exclusion

For factor degrees `(D,a,c)=(3,2,0)`, the Appendix A degree equation gives
`3(ρ-2s)=2s+1`. If `ρ-2s=1`, it forces `(s,ρ)=(1,3)`; exact coefficients
of the factor equation then contradict the nonzero quadratic leading
coefficient. The remaining `h>1` discriminant and positivity argument is
not included here.
-/

namespace Dixmier
open Polynomial

theorem appendix_A3_degree_relation {ρ s : ℕ} {A B Cc : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1)
    (hB0 : B.eval 0 = 1) (hC0 : Cc.eval 0 = -1)
    (ha : A.natDegree = 2) (hD : B.natDegree = 3)
    (hc : Cc.natDegree = 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*Cc)) :
    2*s+1 = 3*(ρ-2*s) := by
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hA0
    norm_num at hA0
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hC : Cc ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hC0
    norm_num at hC0
  have hid := appendix_factor_degree_identity ρ s A B Cc hsρ hA hB hC
    (by omega) hcomp
  rw [ha,hD,hc] at hid
  have hpos := appendix_factor_h_pos ρ s A B Cc hsρ hA hB hC (by omega) hcomp
  omega

theorem appendix_A3_unit_defect_parameters {ρ s : ℕ} {A B Cc : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1)
    (hB0 : B.eval 0 = 1) (hC0 : Cc.eval 0 = -1)
    (ha : A.natDegree = 2) (hD : B.natDegree = 3)
    (hc : Cc.natDegree = 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*Cc))
    (hunit : ρ-2*s = 1) : s=1 ∧ ρ=3 := by
  have hid := appendix_A3_degree_relation hsρ hA0 hB0 hC0 ha hD hc hcomp
  omega

private theorem appendix_A3_unit_explicit (u v b₁ b₂ b₃ : ℂ)
    (hv : v ≠ 0)
    (hpoly :
      let A : ℂ[X] := 1 + C u * X + C v * X^2;
      let B : ℂ[X] := 1 + C b₁ * X + C b₂ * X^2 + C b₃ * X^3;
      -X*(A*derivative B - derivative A*B)+A*B-1=0) : False := by
  dsimp at hpoly
  have hdA : derivative (1 + C u * X + C v * X^2 : ℂ[X]) =
      C u + C (2*v)*X := by
    simp [derivative_add, derivative_X, derivative_pow]
    ring
  have hdB : derivative (1 + C b₁ * X + C b₂ * X^2 + C b₃ * X^3 : ℂ[X]) =
      C b₁ + C (2*b₂)*X + C (3*b₃)*X^2 := by
    simp [derivative_add, derivative_X, derivative_pow]
    ring
  rw [hdA,hdB] at hpoly
  ring_nf at hpoly
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hpoly
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hpoly
  have h3 := congrArg (fun p : ℂ[X] => p.coeff 3) hpoly
  have h4 := congrArg (fun p : ℂ[X] => p.coeff 4) hpoly
  -- Expand the four coefficient identities.
  simp only [coeff_zero] at h1 h2 h3 h4
  norm_num [coeff_add, coeff_sub, coeff_X_pow_mul', coeff_mul_X_pow',
    coeff_C_mul, coeff_X_pow, coeff_C, coeff_one, mul_assoc] at h1 h2 h3 h4
  simp only [coeff_X] at h2 h3 h4
  rw [h1] at h2 h4
  ring_nf at h2 h4
  have hvb₂ : v*b₂=0 := by linear_combination h4
  have hb₂ : b₂=0 := (mul_eq_zero.mp hvb₂).resolve_left hv
  rw [hb₂] at h2
  apply hv
  linear_combination (1/3 : ℂ)*h2

theorem appendix_A3_quadratic_expansion {A : ℂ[X]}
    (hdeg : A.natDegree = 2) (hA0 : A.eval 0 = 1) :
    A = 1 + C (A.coeff 1)*X + C (A.coeff 2)*X^2 := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [coeff_add, coeff_C_mul, coeff_X_pow,
      coeff_one, coeff_zero_eq_eval_zero, hA0]
  · have hz : A.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    simp [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show n ≠ 0 by omega, show 1 ≠ n by omega, show n ≠ 2 by omega]

theorem appendix_A3_cubic_expansion {B : ℂ[X]}
    (hdeg : B.natDegree = 3) (hB0 : B.eval 0 = 1) :
    B = 1 + C (B.coeff 1)*X + C (B.coeff 2)*X^2 + C (B.coeff 3)*X^3 := by
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [coeff_add, coeff_C_mul, coeff_X_pow,
      coeff_one, coeff_zero_eq_eval_zero, hB0]
  · have hz : B.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    simp [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show n ≠ 0 by omega, show 1 ≠ n by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega]

theorem appendix_A3_h_gt_one {ρ s : ℕ} {A B Cc : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1)
    (hB0 : B.eval 0 = 1) (hC0 : Cc.eval 0 = -1)
    (ha : A.natDegree = 2) (hD : B.natDegree = 3)
    (hc : Cc.natDegree = 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*Cc)) : 2*s+1 < ρ := by
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hA0
    norm_num at hA0
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hC : Cc ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hC0
    norm_num at hC0
  have hpos := appendix_factor_h_pos ρ s A B Cc hsρ hA hB hC (by omega) hcomp
  by_contra hn
  have hunit : ρ-2*s=1 := by omega
  obtain ⟨hs1,hρ3⟩ := appendix_A3_unit_defect_parameters hsρ hA0 hB0 hC0
    ha hD hc hcomp hunit
  have hCc : Cc = -1 := by
    rw [eq_C_of_natDegree_eq_zero hc, coeff_zero_eq_eval_zero, hC0]
    simp
  have hcomp' : Comp 3 1 (A*B^2) (A*B*Cc) := by
    simpa [hs1,hρ3] using hcomp
  have hCE : CompanionEq (3 : ℤ) (1 : ℤ) (A*B^2) (A*B*Cc) :=
    (companionEq_natCast_iff 3 1 (A*B^2) (A*B*Cc)).mpr hcomp'
  have hfactor := factor_equation_of_companion 3 1 A B Cc hA hB hCE
  rw [hCc] at hfactor
  have hpoly : -X*(A*derivative B-derivative A*B)+A*B-1=0 := by
    norm_num [derivative_neg, derivative_one] at hfactor
    linear_combination hfactor
  have hAexp := appendix_A3_quadratic_expansion ha hA0
  have hBexp := appendix_A3_cubic_expansion hD hB0
  have hv : A.coeff 2 ≠ 0 := by
    rw [← ha]
    exact leadingCoeff_ne_zero.mpr hA
  rw [hAexp,hBexp] at hpoly
  exact appendix_A3_unit_explicit (A.coeff 1) (A.coeff 2)
    (B.coeff 1) (B.coeff 2) (B.coeff 3) hv hpoly

end Dixmier
