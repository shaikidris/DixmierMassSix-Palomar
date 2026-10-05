/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Equation
public import DixmierFormal.Scalar.AppendixA3ThirdSign

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- A normalized quadratic–cubic Appendix A.3 companion pair has positive real
coefficients in every degree of both factors. -/
theorem appendix_A3_normalized_positive {ρ s : ℕ} {A B : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1) (hB0 : B.eval 0 = 1)
    (hAdeg : A.natDegree = 2) (hBdeg : B.natDegree = 3)
    (hu : A.coeff 1 = 1)
    (hcomp : Comp ρ s (A*B^2) (A*B*(-1))) :
    (∀ i ≤ 2, ∃ x : ℝ, 0 < x ∧ A.coeff i = (x : ℂ)) ∧
    (∀ j ≤ 3, ∃ x : ℝ, 0 < x ∧ B.coeff j = (x : ℂ)) := by
  let h : ℕ := ρ-2*s
  have hgt0 := appendix_A3_h_gt_one hsρ hA0 hB0
    (by norm_num : Polynomial.eval 0 (-1 : ℂ[X]) = -1)
    hAdeg hBdeg (by norm_num : (-1 : ℂ[X]).natDegree = 0) hcomp
  have hgt : 1 < h := by dsimp [h]; omega
  have hrel_nat : 2*s+1=3*h := appendix_A3_degree_relation hsρ hA0 hB0
    (by norm_num : Polynomial.eval 0 (-1 : ℂ[X]) = -1)
    hAdeg hBdeg (by norm_num : (-1 : ℂ[X]).natDegree = 0) hcomp
  have hrel : 2*(s:ℂ)+1=3*(h:ℂ) := by exact_mod_cast hrel_nat
  have hh1 : (h:ℂ) ≠ 1 := by exact_mod_cast (by omega : h ≠ 1)
  have hh2 : 2*(h:ℂ) ≠ 1 := by exact_mod_cast (by omega : 2*h ≠ 1)
  have hh3 : 3*(h:ℂ) ≠ 1 := by exact_mod_cast (by omega : 3*h ≠ 1)
  have heq := appendix_A3_normalized_factor_equation hsρ hA0 hB0 hAdeg hBdeg hu hcomp
  dsimp [h] at heq
  have hphi : appendix_A3_phi (h:ℂ) (A.coeff 2)=0 :=
    appendix_A3_residual (h:ℂ) (s:ℂ) (A.coeff 2)
      (B.coeff 1) (B.coeff 2) (B.coeff 3) hrel hh1 hh2 hh3 heq
  have hgreal : (1:ℝ) < (h:ℝ) := by exact_mod_cast hgt
  have him : (A.coeff 2).im=0 := by
    exact appendix_A3_complex_root_real hgreal (by simpa using hphi)
  have hvreal : A.coeff 2 = ((A.coeff 2).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hphiReal : 48*(h:ℝ)^2*(A.coeff 2).re^2-24*(h:ℝ)*((h:ℝ)+1)*(A.coeff 2).re+
      3*(h:ℝ)^2+4*(h:ℝ)+1=0 := by
    dsimp [appendix_A3_phi] at hphi
    rw [hvreal] at hphi
    exact_mod_cast hphi
  have hvpos : 0 < (A.coeff 2).re := appendix_A3_real_root_pos hgreal hphiReal
  have hb1 := appendix_A3_b1_formula (h:ℂ) (s:ℂ) (A.coeff 2)
    (B.coeff 1) (B.coeff 2) (B.coeff 3) hrel hh1 heq
  have hb2 := appendix_A3_b2_formula (h:ℂ) (s:ℂ) (A.coeff 2)
    (B.coeff 1) (B.coeff 2) (B.coeff 3) hrel hh1 hh2 heq
  have hb3 := appendix_A3_b3_formula (h:ℂ) (s:ℂ) (A.coeff 2)
    (B.coeff 1) (B.coeff 2) (B.coeff 3) hrel hh1 hh2 hh3 heq
  constructor
  · intro i hi
    interval_cases i
    · refine ⟨1, by norm_num, ?_⟩
      simpa [coeff_zero_eq_eval_zero] using hA0
    · refine ⟨1, by norm_num, ?_⟩
      exact hu
    · exact ⟨(A.coeff 2).re,hvpos,hvreal⟩
  · intro j hj
    interval_cases j
    · refine ⟨1, by norm_num, ?_⟩
      simpa [coeff_zero_eq_eval_zero] using hB0
    · let x : ℝ := (3*(h:ℝ)+1)/(2*((h:ℝ)-1))
      refine ⟨x, appendix_A3_b1_real_formula_pos hgreal, ?_⟩
      dsimp [x]
      rw [hb1]
      norm_cast
    · let x : ℝ := (12*(h:ℝ)*((h:ℝ)-1)*(A.coeff 2).re+3*(h:ℝ)^2+4*(h:ℝ)+1)/
        (4*((h:ℝ)-1)*(2*(h:ℝ)-1))
      refine ⟨x, appendix_A3_b2_real_formula_pos hgreal hvpos, ?_⟩
      dsimp [x]
      rw [hb2,hvreal]
      norm_cast
    · let x : ℝ := (((h:ℝ)+1)*(4*(h:ℝ)*(9*(h:ℝ)-5)*(A.coeff 2).re-
          ((h:ℝ)-1)*(3*(h:ℝ)+1)))/(8*((h:ℝ)-1)*(2*(h:ℝ)-1)*(3*(h:ℝ)-1))
      refine ⟨x, appendix_A3_b3_real_formula_pos hgreal hphiReal, ?_⟩
      dsimp [x]
      rw [hb3,hvreal]
      norm_cast

end Dixmier
