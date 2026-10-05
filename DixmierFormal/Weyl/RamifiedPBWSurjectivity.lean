/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedPBWReconstruction

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite ramified PBW data realize actual operators

This is the converse of canonical PBW reconstruction: every finite
Laurent-coefficient sequence defines an operator in the ramified Weyl
algebra, and the canonical coefficients recover that sequence exactly.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedOperatorOfCoeffs (l : ℕ)
    (a : ℕ →₀ LaurentPolynomial ℂ) : ramifiedOperatorAlgebra l :=
  a.sum fun j f => ramifiedCoeffGen l f * (ramifiedYGen l)^j

theorem ramifiedOperatorOfCoeffs_eval (l : ℕ)
    (a : ℕ →₀ LaurentPolynomial ℂ) :
    ((ramifiedOperatorOfCoeffs l a : ramifiedOperatorAlgebra l) :
      Module.End ℂ (LaurentPolynomial ℂ)) = ramifiedNormalEval l a := by
  classical
  simp [ramifiedOperatorOfCoeffs, ramifiedNormalEval,
    ramifiedCoeffGen, ramifiedYGen, Finsupp.sum]

theorem ramifiedPBWCoeffs_operatorOfCoeffs
    (l : ℕ) (hl : 0 < l) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedPBWCoeffs l hl (ramifiedOperatorOfCoeffs l a) = a := by
  apply ramifiedPBWCoeffs_eq_of_eval
  exact (ramifiedOperatorOfCoeffs_eval l a).symm

theorem ramifiedPBWCoeffs_surjective
    (l : ℕ) (hl : 0 < l) :
    Function.Surjective (ramifiedPBWCoeffs l hl) := by
  intro a
  exact ⟨ramifiedOperatorOfCoeffs l a,
    ramifiedPBWCoeffs_operatorOfCoeffs l hl a⟩

theorem ramifiedOperatorOfCoeffs_pbwCoeffs
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l) :
    ramifiedOperatorOfCoeffs l (ramifiedPBWCoeffs l hl T) = T := by
  exact ramifiedPBW_reconstruct l hl T

/-- Exact, cutoff-free correspondence between finite Laurent PBW data
and operators in the ramified Weyl algebra. -/
noncomputable def ramifiedPBWEquiv (l : ℕ) (hl : 0 < l) :
    ramifiedOperatorAlgebra l ≃ (ℕ →₀ LaurentPolynomial ℂ) where
  toFun := ramifiedPBWCoeffs l hl
  invFun := ramifiedOperatorOfCoeffs l
  left_inv := ramifiedOperatorOfCoeffs_pbwCoeffs l hl
  right_inv := ramifiedPBWCoeffs_operatorOfCoeffs l hl

end Dixmier.Weyl
