/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2Signs
public import DixmierFormal.Scalar.Scaling

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.2: linear-factor normalization

A degree-one companion factor with constant term `-1` has shape `aX-1`.
Rescaling by `a⁻¹` gives the normalized factor `X-1` and preserves the
companion equation, degree, constant term, and all power term counts.
-/

namespace Dixmier
open Polynomial

theorem appendix_A2_linear_companion_shape {Cc : ℂ[X]}
    (hdeg : Cc.natDegree = 1) (hC0 : Cc.eval 0 = -1) :
    ∃ alpha : ℂ, alpha ≠ 0 ∧ Cc = C alpha * X - 1 := by
  rcases (natDegree_eq_one (p := Cc)).mp hdeg with ⟨alpha,halpha,b,hshape⟩
  have hb : b = -1 := by
    have hev := congrArg (fun p : ℂ[X] => p.eval 0) hshape
    simpa [hC0] using hev
  refine ⟨alpha,halpha,?_⟩
  rw [← hshape, hb]
  simp only [map_neg, map_one]
  ring

theorem appendix_A2_scale_linear {Cc : ℂ[X]} {alpha : ℂ}
    (halpha : alpha ≠ 0) (hC : Cc = C alpha * X - 1) :
    Cc.comp (C alpha⁻¹ * X) = X-1 := by
  rw [hC, sub_comp, mul_comp, C_comp, X_comp, one_comp]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ halpha, C_1, one_mul]

theorem appendix_A2_normalize_general_linear {ρ s : ℕ} {B Cc : ℂ[X]}
    (hCdeg : Cc.natDegree = 1) (hC0 : Cc.eval 0 = -1)
    (hB0 : B.eval 0 = 1) (hcomp : Comp ρ s (B^2) (B*Cc)) :
    ∃ Bn : ℂ[X], Comp ρ s (Bn^2) (Bn*(X-1)) ∧
      Bn.natDegree = B.natDegree ∧ Bn.eval 0 = 1 ∧
      ∀ k : ℕ, termCount (Bn^(2*k)) = termCount (B^(2*k)) := by
  obtain ⟨alpha,halpha,hCshape⟩ := appendix_A2_linear_companion_shape hCdeg hC0
  let Bn := B.comp (C alpha⁻¹ * X)
  have hc : Cc.comp (C alpha⁻¹ * X) = X-1 :=
    appendix_A2_scale_linear halpha hCshape
  have hcomp' := hcomp.comp_C_mul_X alpha⁻¹
  have hnorm : Comp ρ s (Bn^2) (Bn*(X-1)) := by
    simpa only [Bn, pow_comp, mul_comp, hc] using hcomp'
  refine ⟨Bn,hnorm,?_,?_,?_⟩
  · exact natDegree_comp_C_mul_X (inv_ne_zero halpha)
  · simpa only [Bn, eval_zero_comp_C_mul_X] using hB0
  · intro k
    simpa only [Bn, pow_comp] using
      (termCount_comp_C_mul_X (p := B^(2*k)) (inv_ne_zero halpha))

end Dixmier
