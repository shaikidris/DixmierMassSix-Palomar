/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedShearBase

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite PBW substitution at a shifted ramified derivative

The unique PBW coefficient sequence defines a linear substitution
`∑ M_(a_j) Y^j ↦ ∑ M_(a_j) (Y+M_h)^j`. It maps into the same generated
operator algebra, fixes all coefficient generators, sends `Y` to `Y+M_h`,
and is the identity for `h=0`. Multiplicativity, inverse substitution,
and G13's cut are not claimed in this file.
-/
namespace Dixmier.Weyl

/-- Evaluate a finite PBW sequence at the shifted generator. -/
noncomputable def ramifiedShiftEval (l : ℕ) (h : LaurentPolynomial ℂ)
    (a : ℕ →₀ LaurentPolynomial ℂ) :
    Module.End ℂ (LaurentPolynomial ℂ) :=
  a.sum fun j f => ramifiedCoeffMul f * (ramifiedShiftedY l h)^j

theorem ramifiedShiftedY_mem (l : ℕ) (h : LaurentPolynomial ℂ) :
    ramifiedShiftedY l h ∈ ramifiedOperatorAlgebra l := by
  exact (ramifiedOperatorAlgebra l).add_mem
    (derivative_mem_ramifiedOperatorAlgebra l)
    (coeff_mem_ramifiedOperatorAlgebra l h)

theorem ramifiedShiftEval_mem (l : ℕ) (h : LaurentPolynomial ℂ)
    (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedShiftEval l h a ∈ ramifiedOperatorAlgebra l := by
  classical
  unfold ramifiedShiftEval Finsupp.sum
  apply Subalgebra.sum_mem
  intro j hj
  exact (ramifiedOperatorAlgebra l).mul_mem
    (coeff_mem_ramifiedOperatorAlgebra l (a j))
    ((ramifiedOperatorAlgebra l).pow_mem (ramifiedShiftedY_mem l h) j)

/-- The candidate shear on a ramified operator, defined by its unique
finite PBW expansion. -/
noncomputable def ramifiedShearCandidate (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedOperatorAlgebra l :=
  ⟨ramifiedShiftEval l h (ramifiedPBWCoeffs l hl T),
    ramifiedShiftEval_mem l h _⟩

theorem ramifiedShiftEval_single (l : ℕ) (h f : LaurentPolynomial ℂ)
    (j : ℕ) :
    ramifiedShiftEval l h (Finsupp.single j f) =
      ramifiedCoeffMul f * (ramifiedShiftedY l h)^j := by
  unfold ramifiedShiftEval
  rw [Finsupp.sum_single_index]
  simp [ramifiedCoeffMul]

noncomputable def ramifiedCoeffGen (l : ℕ) (f : LaurentPolynomial ℂ) :
    ramifiedOperatorAlgebra l :=
  ⟨ramifiedCoeffMul f, coeff_mem_ramifiedOperatorAlgebra l f⟩

noncomputable def ramifiedYGen (l : ℕ) : ramifiedOperatorAlgebra l :=
  ⟨ramifiedDerivative l, derivative_mem_ramifiedOperatorAlgebra l⟩

theorem ramifiedPBWCoeffs_coeffGen (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) :
    ramifiedPBWCoeffs l hl (ramifiedCoeffGen l f) = Finsupp.single 0 f := by
  apply ramifiedPBWCoeffs_eq_of_eval
  have hs := ramifiedNormalEvalLinear_single l 0 f
  simpa [ramifiedNormalEvalLinear_apply, ramifiedCoeffGen] using hs

theorem ramifiedPBWCoeffs_YGen (l : ℕ) (hl : 0 < l) :
    ramifiedPBWCoeffs l hl (ramifiedYGen l) =
      Finsupp.single 1 (1 : LaurentPolynomial ℂ) := by
  apply ramifiedPBWCoeffs_eq_of_eval
  have hs := ramifiedNormalEvalLinear_single l 1
    (1 : LaurentPolynomial ℂ)
  simpa [ramifiedNormalEvalLinear_apply, ramifiedYGen,
    ramifiedCoeffMul_one] using hs

theorem ramifiedShearCandidate_coeffGen (l : ℕ) (hl : 0 < l)
    (h f : LaurentPolynomial ℂ) :
    ramifiedShearCandidate l hl h (ramifiedCoeffGen l f) =
      ramifiedCoeffGen l f := by
  apply Subtype.ext
  change ramifiedShiftEval l h
    (ramifiedPBWCoeffs l hl (ramifiedCoeffGen l f)) = ramifiedCoeffMul f
  rw [ramifiedPBWCoeffs_coeffGen, ramifiedShiftEval_single]
  simp

theorem ramifiedShearCandidate_YGen (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    (ramifiedShearCandidate l hl h (ramifiedYGen l) :
      Module.End ℂ (LaurentPolynomial ℂ)) = ramifiedShiftedY l h := by
  change ramifiedShiftEval l h (ramifiedPBWCoeffs l hl (ramifiedYGen l)) = _
  rw [ramifiedPBWCoeffs_YGen, ramifiedShiftEval_single]
  simp [ramifiedCoeffMul_one]

theorem ramifiedShiftedY_zero (l : ℕ) :
    ramifiedShiftedY l 0 = ramifiedDerivative l := by
  simp [ramifiedShiftedY, ramifiedCoeffMul]

theorem ramifiedShearCandidate_zero (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl 0 T = T := by
  apply Subtype.ext
  change ramifiedShiftEval l 0 (ramifiedPBWCoeffs l hl T) =
    (T : Module.End ℂ (LaurentPolynomial ℂ))
  have heval := ramifiedPBWCoeffs_eval l hl T
  simpa [ramifiedShiftEval, ramifiedNormalEval, ramifiedShiftedY_zero] using heval

noncomputable def ramifiedShiftEvalLinear (l : ℕ)
    (h : LaurentPolynomial ℂ) :
    (ℕ →₀ LaurentPolynomial ℂ) →ₗ[ℂ]
      Module.End ℂ (LaurentPolynomial ℂ) :=
  (Finsupp.lsum ℂ) (fun n =>
    (LinearMap.mulRight ℂ ((ramifiedShiftedY l h)^n)).comp
      ramifiedCoeffMulLinear)

theorem ramifiedShiftEvalLinear_apply (l : ℕ) (h : LaurentPolynomial ℂ)
    (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedShiftEvalLinear l h a = ramifiedShiftEval l h a := by
  rfl

theorem ramifiedPBWCoeffs_add (l : ℕ) (hl : 0 < l)
    (T U : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (T+U) =
      ramifiedPBWCoeffs l hl T + ramifiedPBWCoeffs l hl U := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [← ramifiedNormalEvalLinear_apply, map_add,
    ramifiedNormalEvalLinear_apply, ramifiedNormalEvalLinear_apply,
    ramifiedPBWCoeffs_eval, ramifiedPBWCoeffs_eval]
  rfl

theorem ramifiedPBWCoeffs_smul (l : ℕ) (hl : 0 < l)
    (c : ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (c • T) = c • ramifiedPBWCoeffs l hl T := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [← ramifiedNormalEvalLinear_apply, map_smul,
    ramifiedNormalEvalLinear_apply, ramifiedPBWCoeffs_eval]
  rfl

theorem ramifiedShearCandidate_add (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (T U : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl h (T+U) =
      ramifiedShearCandidate l hl h T + ramifiedShearCandidate l hl h U := by
  apply Subtype.ext
  change ramifiedShiftEval l h (ramifiedPBWCoeffs l hl (T+U)) =
    ramifiedShiftEval l h (ramifiedPBWCoeffs l hl T) +
      ramifiedShiftEval l h (ramifiedPBWCoeffs l hl U)
  rw [ramifiedPBWCoeffs_add,
    ← ramifiedShiftEvalLinear_apply,
    map_add, ramifiedShiftEvalLinear_apply, ramifiedShiftEvalLinear_apply]

theorem ramifiedShearCandidate_smul (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (c : ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl h (c • T) =
      c • ramifiedShearCandidate l hl h T := by
  apply Subtype.ext
  change ramifiedShiftEval l h (ramifiedPBWCoeffs l hl (c • T)) =
    c • ramifiedShiftEval l h (ramifiedPBWCoeffs l hl T)
  rw [ramifiedPBWCoeffs_smul,
    ← ramifiedShiftEvalLinear_apply,
    map_smul, ramifiedShiftEvalLinear_apply]

/-- The PBW substitution is linear. Its algebra-homomorphism property
remains to be proved. -/
noncomputable def ramifiedShearLinear (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedOperatorAlgebra l →ₗ[ℂ] ramifiedOperatorAlgebra l where
  toFun := ramifiedShearCandidate l hl h
  map_add' := ramifiedShearCandidate_add l hl h
  map_smul' := ramifiedShearCandidate_smul l hl h

end Dixmier.Weyl
