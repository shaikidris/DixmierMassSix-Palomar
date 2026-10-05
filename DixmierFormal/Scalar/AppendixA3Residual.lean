/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Formulas

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier
open Polynomial

def appendix_A3_phi (h v : ℂ) : ℂ :=
  48*h^2*v^2-24*h*(h+1)*v+3*h^2+4*h+1

theorem appendix_A3_discriminant (h : ℝ) :
    (24*h*(h+1))^2-4*(48*h^2)*(3*h^2+4*h+1)=384*h^2*(h+1) := by
  ring

theorem appendix_A3_discriminant_pos {h : ℝ} (hh : 1 < h) :
    0 < (24*h*(h+1))^2-4*(48*h^2)*(3*h^2+4*h+1) := by
  rw [appendix_A3_discriminant]
  positivity

theorem appendix_A3_residual (h s v b₁ b₂ b₃ : ℂ)
    (hrel : 2*s+1=3*h) (hh1 : h≠1) (hh2 : 2*h≠1) (hh3 : 3*h≠1)
    (heq :
      let A : ℂ[X] := 1+C (1:ℂ)*X+C v*X^2;
      let B : ℂ[X] := 1+C b₁*X+C b₂*X^2+C b₃*X^3;
      -X*(C h*A*derivative B-C s*derivative A*B)+A*B-1=0) :
    appendix_A3_phi h v=0 := by
  obtain ⟨_,_,_,h4⟩ := appendix_A3_coeff_equations h s 1 v b₁ b₂ b₃ heq
  have hb2 := appendix_A3_b2_formula h s v b₁ b₂ b₃ hrel hh1 hh2 heq
  have hb3 := appendix_A3_b3_formula h s v b₁ b₂ b₃ hrel hh1 hh2 hh3 heq
  rw [hb2,hb3] at h4
  have hs : s=(3*h-1)/2 := by linear_combination (1/2)*hrel
  rw [hs] at h4
  have hd1 : h-1 ≠ 0 := sub_ne_zero.mpr hh1
  have hd2 : 2*h-1 ≠ 0 := sub_ne_zero.mpr hh2
  have hd3 : 3*h-1 ≠ 0 := sub_ne_zero.mpr hh3
  have hd2' : h*2-1 ≠ 0 := by simpa [mul_comm] using hd2
  field_simp [hd1,hd2,hd2',hd3] at h4
  have hprod : 4*(h-1)*(3*h-1)*appendix_A3_phi h v=0 := by
    dsimp [appendix_A3_phi]
    linear_combination h4
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hd1) hd3)

end Dixmier
