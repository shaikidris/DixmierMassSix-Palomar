/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Boundary

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier
open Polynomial

theorem appendix_A3_coeff_equations (h s u v b₁ b₂ b₃ : ℂ)
    (heq :
      let A : ℂ[X] := 1+C u*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) :
    ((1-h)*b₁+(1+s)*u=0) ∧
    ((1-2*h)*b₂+(1-h+s)*u*b₁+(1+2*s)*v=0) ∧
    ((1-3*h)*b₃+(1-2*h+s)*u*b₂+(1-h+2*s)*v*b₁=0) ∧
    ((1-3*h+s)*u*b₃+(1-2*h+2*s)*v*b₂=0) := by
  dsimp at heq
  have hdA : derivative (1+C u*X+C v*X^2 : ℂ[X]) = C u+C (2*v)*X := by
    simp [derivative_add, derivative_X, derivative_pow]
    ring
  have hdB : derivative (1+C b₁*X+C b₂*X^2+C b₃*X^3 : ℂ[X]) =
      C b₁+C (2*b₂)*X+C (3*b₃)*X^2 := by
    simp [derivative_add, derivative_X, derivative_pow]
    ring
  rw [hdA,hdB] at heq
  ring_nf at heq
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) heq
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) heq
  have h3 := congrArg (fun p : ℂ[X] => p.coeff 3) heq
  have h4 := congrArg (fun p : ℂ[X] => p.coeff 4) heq
  simp only [coeff_zero] at h1 h2 h3 h4
  norm_num [coeff_add, coeff_sub, coeff_X_pow_mul', coeff_mul_X_pow',
    coeff_C_mul, coeff_X_pow, coeff_C, coeff_one, mul_assoc] at h1 h2 h3 h4
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4

theorem appendix_A3_linear_coeff_nonzero (h s u v b₁ b₂ b₃ : ℂ)
    (hh1 : h ≠ 1) (hh3 : 3*h ≠ 1) (hb₃ : b₃ ≠ 0)
    (heq :
      let A : ℂ[X] := 1+C u*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) : u ≠ 0 := by
  obtain ⟨h1,_,h3,_⟩ := appendix_A3_coeff_equations h s u v b₁ b₂ b₃ heq
  intro hu
  rw [hu] at h1 h3
  simp only [mul_zero, add_zero, zero_mul] at h1 h3
  have hb₁ : b₁=0 := by
    have hfac : 1-h ≠ 0 := sub_ne_zero.mpr hh1.symm
    exact (mul_eq_zero.mp h1).resolve_left hfac
  rw [hb₁] at h3
  simp only [mul_zero, add_zero] at h3
  have hfac : 1-3*h ≠ 0 := sub_ne_zero.mpr hh3.symm
  exact hb₃ ((mul_eq_zero.mp h3).resolve_left hfac)

theorem appendix_A3_A_linear_nonzero {ρ s : ℕ} {A B Cc : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1)
    (hB0 : B.eval 0 = 1) (hC0 : Cc.eval 0 = -1)
    (ha : A.natDegree = 2) (hD : B.natDegree = 3)
    (hc : Cc.natDegree = 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*Cc)) : A.coeff 1 ≠ 0 := by
  have hgt := appendix_A3_h_gt_one hsρ hA0 hB0 hC0 ha hD hc hcomp
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hA0
    norm_num at hA0
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hCc : Cc = -1 := by
    rw [eq_C_of_natDegree_eq_zero hc, coeff_zero_eq_eval_zero, hC0]
    simp
  have hCE : CompanionEq (ρ : ℤ) (s : ℤ) (A*B^2) (A*B*Cc) :=
    (companionEq_natCast_iff ρ s (A*B^2) (A*B*Cc)).mpr hcomp
  have hfactor := factor_equation_of_companion (ρ : ℤ) (s : ℤ) A B Cc hA hB hCE
  rw [hCc] at hfactor
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
  have hAexp := appendix_A3_quadratic_expansion ha hA0
  have hBexp := appendix_A3_cubic_expansion hD hB0
  have hb₃ : B.coeff 3 ≠ 0 := by
    rw [← hD]
    exact leadingCoeff_ne_zero.mpr hB
  have hh1 : (h : ℂ) ≠ 1 := by
    exact_mod_cast (by dsimp [h]; omega : h ≠ 1)
  have hh3 : (3 : ℂ)*(h : ℂ) ≠ 1 := by
    exact_mod_cast (by dsimp [h]; omega : 3*h ≠ 1)
  rw [hAexp,hBexp] at hpoly
  exact appendix_A3_linear_coeff_nonzero (h : ℂ) (s : ℂ)
    (A.coeff 1) (A.coeff 2) (B.coeff 1) (B.coeff 2) (B.coeff 3)
    hh1 hh3 hb₃ hpoly

end Dixmier
