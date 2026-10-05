/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Coefficients

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier
open Polynomial

theorem appendix_A3_b1_formula (h s v b₁ b₂ b₃ : ℂ)
    (hrel : 2*s+1=3*h) (hh1 : h≠1)
    (heq :
      let A : ℂ[X] := 1+C (1:ℂ)*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) :
    b₁=(3*h+1)/(2*(h-1)) := by
  obtain ⟨h1,_,_,_⟩ := appendix_A3_coeff_equations h s 1 v b₁ b₂ b₃ heq
  have hd : 2*(h-1) ≠ 0 := by exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hh1)
  apply (eq_div_iff hd).2
  linear_combination -2*h1+hrel

theorem appendix_A3_b2_formula (h s v b₁ b₂ b₃ : ℂ)
    (hrel : 2*s+1=3*h) (hh1 : h≠1) (hh2 : 2*h≠1)
    (heq :
      let A : ℂ[X] := 1+C (1:ℂ)*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) :
    b₂=(12*h*(h-1)*v+3*h^2+4*h+1)/(4*(h-1)*(2*h-1)) := by
  obtain ⟨_,h2,_,_⟩ := appendix_A3_coeff_equations h s 1 v b₁ b₂ b₃ heq
  have hb1 := appendix_A3_b1_formula h s v b₁ b₂ b₃ hrel hh1 heq
  rw [hb1] at h2
  have hs : s=(3*h-1)/2 := by linear_combination (1/2)*hrel
  rw [hs] at h2
  have hd1 : h-1 ≠ 0 := sub_ne_zero.mpr hh1
  have hd2 : 2*h-1 ≠ 0 := sub_ne_zero.mpr hh2
  have hd : 4*(h-1)*(2*h-1) ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) hd1) hd2
  apply (eq_div_iff hd).2
  field_simp [hd1] at h2
  linear_combination -h2

theorem appendix_A3_b3_formula (h s v b₁ b₂ b₃ : ℂ)
    (hrel : 2*s+1=3*h) (hh1 : h≠1) (hh2 : 2*h≠1) (hh3 : 3*h≠1)
    (heq :
      let A : ℂ[X] := 1+C (1:ℂ)*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) :
    b₃=((h+1)*(4*h*(9*h-5)*v-(h-1)*(3*h+1)))/
      (8*(h-1)*(2*h-1)*(3*h-1)) := by
  obtain ⟨_,_,h3,_⟩ := appendix_A3_coeff_equations h s 1 v b₁ b₂ b₃ heq
  have hb1 := appendix_A3_b1_formula h s v b₁ b₂ b₃ hrel hh1 heq
  have hb2 := appendix_A3_b2_formula h s v b₁ b₂ b₃ hrel hh1 hh2 heq
  rw [hb1,hb2] at h3
  have hs : s=(3*h-1)/2 := by linear_combination (1/2)*hrel
  rw [hs] at h3
  have hd1 : h-1 ≠ 0 := sub_ne_zero.mpr hh1
  have hd2 : 2*h-1 ≠ 0 := sub_ne_zero.mpr hh2
  have hd3 : 3*h-1 ≠ 0 := sub_ne_zero.mpr hh3
  have hd2' : h*2-1 ≠ 0 := by simpa [mul_comm] using hd2
  have hd : 8*(h-1)*(2*h-1)*(3*h-1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hd1) hd2) hd3
  apply (eq_div_iff hd).2
  field_simp [hd1,hd2,hd2'] at h3
  linear_combination -h3

end Dixmier
