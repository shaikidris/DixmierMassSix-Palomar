/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2Power

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier
open Polynomial

/-- A complex polynomial with positive real coefficients in every degree from
zero through `D` has full support in every power. This reuses the signed-power
theorem after the substitution `X ↦ -X`. -/
theorem positive_complex_dense_power_termCount {B : ℂ[X]} {D : ℕ}
    (hdeg : B.natDegree ≤ D)
    (hpos : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧ B.coeff n = (x : ℂ))
    (k : ℕ) : termCount (B^k) = k*D+1 := by
  let S := B.comp (C (-1 : ℂ)*X)
  have hSdeg : S.natDegree ≤ D := by
    exact (natDegree_comp_C_mul_X (p := B) (by norm_num : (-1 : ℂ) ≠ 0)).le.trans hdeg
  have hsign : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      S.coeff n = (((-1 : ℝ)^n * x : ℝ) : ℂ) := by
    intro n hn
    obtain ⟨x,hx,hxn⟩ := hpos n hn
    refine ⟨x,hx,?_⟩
    change (B.comp (C (-1 : ℂ)*X)).coeff n = _
    rw [coeff_comp_C_mul_X, hxn]
    push_cast
    ring
  have htc := signed_dense_power_termCount hSdeg hsign k
  have hscale : termCount (S^k) = termCount (B^k) := by
    simpa only [S, pow_comp] using
      (termCount_comp_C_mul_X (p := B^k) (by norm_num : (-1 : ℂ) ≠ 0))
  rw [hscale] at htc
  exact htc

end Dixmier
