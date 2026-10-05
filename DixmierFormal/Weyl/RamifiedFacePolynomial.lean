/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutEdgeCoeff
public import Mathlib.Algebra.Polynomial.AlgebraMap

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A finite scalar polynomial for a ramified PBW face

At a fixed weight, the exponent of `T` is determined by the exponent of
`Y`. Thus the coefficients of one face form an ordinary polynomial. A
translation of this polynomial cannot make a nonzero face vanish.
-/
namespace Dixmier.Weyl

/-- Coefficients on the affine lattice `i = r-kj` of a finite PBW operator. -/
noncomputable def ramifiedFacePolynomial (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (r k : ℤ) : Polynomial ℂ :=
  Polynomial.ofFinsupp ⟨
    Finsupp.onFinset (ramifiedPBWCoeffs l hl T).support
      (fun j => ramifiedPBWCoeff l hl T (r - k * (j : ℤ)) j)
      (by
        intro j hj
        apply Finsupp.mem_support_iff.mpr
        intro hz
        simp [ramifiedPBWCoeff, hz] at hj)⟩

@[simp] theorem ramifiedFacePolynomial_coeff (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (r k : ℤ) (j : ℕ) :
    (ramifiedFacePolynomial l hl T r k).coeff j =
      ramifiedPBWCoeff l hl T (r - k * (j : ℤ)) j := by
  simp [ramifiedFacePolynomial]

theorem ramifiedFacePolynomial_ne_zero_of_coeff (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (r k : ℤ) (j : ℕ)
    (hj : ramifiedPBWCoeff l hl T (r - k * (j : ℤ)) j ≠ 0) :
    ramifiedFacePolynomial l hl T r k ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff j) hz
  simpa using hj ((ramifiedFacePolynomial_coeff l hl T r k j).symm.trans hc)

/-- A point at weight `ρr` lies on the single affine lattice indexed by
the derivative exponent. -/
theorem ramifiedCutWeight_point_index (l : ℕ) (ρ σ r i : ℤ)
    (j : ℕ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hw : ramifiedWeight l ρ σ (i,j) = ρ * r) :
    i = r - ramifiedCutExponent l ρ σ * (j : ℤ) := by
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  have heq : ρ * (i + ramifiedCutExponent l ρ σ * (j : ℤ)) =
      ρ * r := by
    dsimp [ramifiedWeight] at hw
    nlinarith [congrArg (fun x : ℤ => x * (j : ℤ)) hk]
  have hcancel : i + ramifiedCutExponent l ρ σ * (j : ℤ) = r :=
    (mul_left_cancel₀ (ne_of_gt hρ)) heq
  omega

/-- An occupied point of the weight-`ρr` face gives a nonzero scalar face. -/
theorem ramifiedFacePolynomial_ne_zero_of_weight_point (l : ℕ)
    (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (ρ σ r i : ℤ) (j : ℕ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ))
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (hw : ramifiedWeight l ρ σ (i,j) = ρ * r) :
    ramifiedFacePolynomial l hl T r
      (ramifiedCutExponent l ρ σ) ≠ 0 := by
  have hi := ramifiedCutWeight_point_index l ρ σ r i j hρ hdiv hw
  apply ramifiedFacePolynomial_ne_zero_of_coeff l hl T _ _ j
  rw [← hi]
  exact (ramifiedPBWSupport_mem_iff l hl T i j).mp hmem

/-- Commutative translation preserves a nonzero finite face. This is the
cancellation argument needed once exact shear coefficients are summed. -/
theorem ramifiedFacePolynomial_translate_ne_zero (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (r k : ℤ) (c : ℂ)
    (hface : ramifiedFacePolynomial l hl T r k ≠ 0) :
    (ramifiedFacePolynomial l hl T r k).comp
      (Polynomial.X + Polynomial.C c) ≠ 0 := by
  exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hface

/-- An occupied weighted face cannot disappear under its commutative
translation. The separate PBW shear-to-translation identity is still
required to apply this to the operator's actual transformed face. -/
theorem ramifiedCutFace_translate_ne_zero_of_weight_point (l : ℕ)
    (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (ρ σ r i : ℤ) (j : ℕ) (c : ℂ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (hw : ramifiedWeight l ρ σ (i,j) = ρ * r) :
    (ramifiedFacePolynomial l hl T r
      (ramifiedCutExponent l ρ σ)).comp
        (Polynomial.X + Polynomial.C c) ≠ 0 := by
  apply ramifiedFacePolynomial_translate_ne_zero
  exact ramifiedFacePolynomial_ne_zero_of_weight_point l hl T
    ρ σ r i j hρ hdiv hmem hw

end Dixmier.Weyl
