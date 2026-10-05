/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedGradeFiltration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# An exact Laurent pair with a negative-grade first member

This control separates the pairwise positive-grade conclusion from a
claim that a specified member has positive grade.
-/

namespace Dixmier.Weyl

open LaurentPolynomial

noncomputable def negativeP : ramifiedOperatorAlgebra 1 :=
  ramifiedCoeffGen 1 (T (-1))

noncomputable def positiveQ : ramifiedOperatorAlgebra 1 :=
  -(ramifiedCoeffGen 1 (T 2) * ramifiedYGen 1)

theorem negativeP_positiveQ_exact :
    positiveQ * negativeP - negativeP * positiveQ = 1 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change -(T 2 * ramifiedDerivative 1 (T (-1) * f)) -
    T (-1) * (-(T 2 * ramifiedDerivative 1 f)) = f
  rw [ramifiedDerivative_mul, ramifiedDerivative_T]
  norm_num
  ring_nf
  simp

theorem negativeP_support_iff (i : ℤ) (j : ℕ) :
    (i,j) ∈ ramifiedPBWSupport 1 (by decide) negativeP ↔
      i = -1 ∧ j = 0 := by
  rw [ramifiedPBWSupport_mem_iff]
  unfold ramifiedPBWCoeff negativeP
  rw [ramifiedPBWCoeffs_coeffGen]
  by_cases hj : j = 0
  · subst j
    simp [eq_comm]
  · simp [Finsupp.single_eq_of_ne hj, hj]

theorem negativeP_has_strictly_negative_grade
    (i : ℤ) (j : ℕ)
    (hij : (i,j) ∈ ramifiedPBWSupport 1 (by decide) negativeP) :
    i - (j : ℤ) < 0 := by
  obtain ⟨rfl,rfl⟩ := (negativeP_support_iff i j).mp hij
  norm_num

end Dixmier.Weyl
