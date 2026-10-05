/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalPoisson

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal homogeneous base shape

A nonzero homogeneous source base has a nonnegative integer x-degree and a
single-variable coefficient. The canonical univariate polynomial evaluates
back to its renamed bivariate coefficient.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem horizontal_nonzero_homogeneous_shape
    (R : MvPolynomial (Fin 2) ℂ) (m : ℤ)
    (hR : R ≠ 0) (hhom : R.IsWeightedHomogeneous (wt 1 0) m) :
    ∃ (a : ℕ) (U : MvPolynomial (Fin 1) ℂ),
      m = a ∧ U ≠ 0 ∧
      R = MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ U := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hR
  obtain ⟨⟨a, b⟩, hda⟩ := expo_surjective d
  subst d
  have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
  rw [expo_weight] at hw
  have hm : m = (a : ℤ) := by omega
  have hhom' : R.IsWeightedHomogeneous (wt 1 0) (a : ℤ) := by
    rw [← hm]
    exact hhom
  obtain ⟨U, hshape⟩ := horizontal_homogeneous_shape R a hhom'
  have hU : U ≠ 0 := by
    intro hz
    rw [hz] at hshape
    simp at hshape
    exact hR hshape
  exact ⟨a, U, hm, hU, hshape⟩

theorem horizontal_rename_eq_eval (U : MvPolynomial (Fin 1) ℂ) :
    MvPolynomial.rename Fin.succ U =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) U).eval₂
        MvPolynomial.C (MvPolynomial.X 1) := by
  induction U using MvPolynomial.induction_on with
  | C c => simp
  | add U V hU hV => simp [hU, hV]
  | mul_X U i ih =>
      fin_cases i
      simp [ih, MvPolynomial.uniqueAlgEquiv_apply]

end Dixmier.Weyl
