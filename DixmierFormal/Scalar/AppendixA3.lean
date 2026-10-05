/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3NormalizedPositive

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- Proposition A.3: every power of the quadratic–cubic factor product has
full support, with no slope, degree-gap, or power cutoff. -/
theorem appendix_A3_termCount {ρ s : ℕ} {A B Cc : ℂ[X]}
    (hsρ : s < ρ) (hA0 : A.eval 0 = 1)
    (hB0 : B.eval 0 = 1) (hC0 : Cc.eval 0 = -1)
    (hAdeg : A.natDegree = 2) (hBdeg : B.natDegree = 3)
    (hCdeg : Cc.natDegree = 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*Cc))
    (k : ℕ) : termCount ((A*B^2)^k) = 8*k+1 := by
  have hCc : Cc = -1 := by
    rw [eq_C_of_natDegree_eq_zero hCdeg, coeff_zero_eq_eval_zero, hC0]
    simp
  have hcompneg : Comp ρ s (A*B^2) (A*B*(-1)) := by
    simpa only [hCc] using hcomp
  have hu : A.coeff 1 ≠ 0 :=
    appendix_A3_A_linear_nonzero hsρ hA0 hB0 hC0 hAdeg hBdeg hCdeg hcomp
  obtain ⟨An,Bn,hcompn,hAdeg_n,hBdeg_n,hAn0,hBn0,hu_n,htc⟩ :=
    appendix_A3_normalize_linear hu hcompneg
  have hAnDeg : An.natDegree = 2 := hAdeg_n.trans hAdeg
  have hBnDeg : Bn.natDegree = 3 := hBdeg_n.trans hBdeg
  have hAnZero : An.eval 0 = 1 := hAn0.trans hA0
  have hBnZero : Bn.eval 0 = 1 := hBn0.trans hB0
  obtain ⟨hApos,hBpos⟩ :=
    appendix_A3_normalized_positive hsρ hAnZero hBnZero hAnDeg hBnDeg hu_n hcompn
  have htc' := positive_complex_quadratic_cubic_square_termCount
    hAnDeg.le hBnDeg.le hApos hBpos k
  exact (htc k).symm.trans htc'

end Dixmier
