/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingCutConsumer

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
/-!
# Horizontal face shape

A polynomial homogeneous for direction `(1,0)` has a single `x`-degree and
therefore separates as `x^ω U(y)`. This is the starting point for a horizontal
mate analysis; it does not by itself identify `U` or exclude the face.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Separate a `(1,0)`-homogeneous bivariate polynomial into its unique
`x`-power and a polynomial in `y`. -/
theorem horizontal_homogeneous_shape
    (F : MvPolynomial (Fin 2) ℂ) (ω : ℕ)
    (hhom : F.IsWeightedHomogeneous (wt 1 0) (ω : ℤ)) :
    ∃ U : MvPolynomial (Fin 1) ℂ,
      F = MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let U := (E F).coeff ω
  have hsupport (i : ℕ) (hi : i ∈ (E F).support) : i = ω := by
    rw [MvPolynomial.support_finSuccEquiv] at hi
    obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp hi
    have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
    obtain ⟨⟨a, b⟩, rfl⟩ := expo_surjective d
    rw [expo_weight] at hw
    have hai : a = i := by simpa [expo] using hd0
    omega
  have hpoly : E F = Polynomial.monomial ω U := by
    apply Polynomial.ext
    intro i
    by_cases hi : i = ω
    · subst i
      simp [U]
    · have hnot : i ∉ (E F).support := by
        intro hmem
        exact hi (hsupport i hmem)
      have hzero : (E F).coeff i = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hnot
      simp [Polynomial.coeff_monomial, hzero, Ne.symm hi]
  have hmap : E (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) =
      Polynomial.monomial ω U := by
    have hx : E (MvPolynomial.X 0) = Polynomial.X := by
      simpa [E] using (MvPolynomial.finSuccEquiv_X_zero (R := ℂ) (n := 1))
    have hy : E (MvPolynomial.rename Fin.succ U) = Polynomial.C U := by
      simpa [E] using finSuccEquiv_rename_succ U
    calc
      E (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) =
          Polynomial.X ^ ω * Polynomial.C U := by
            rw [map_mul, map_pow, hx, hy]
      _ = Polynomial.monomial ω U := by
        rw [mul_comm, Polynomial.C_mul_X_pow_eq_monomial]
  exact ⟨U, E.injective (hpoly.trans hmap.symm)⟩

/-- A positive-weight horizontal operator face has the same separated form,
with a positive integer exponent equal to its actual weighted degree. -/
theorem horizontal_operator_face_shape (T : A1 ℂ)
    (hpos : 0 < vDeg 1 0 T.1) :
    ∃ (ω : ℕ) (U : MvPolynomial (Fin 1) ℂ),
      0 < ω ∧ vDeg 1 0 T.1 = ω ∧
      leadingForm 1 0 T.1 =
        MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U := by
  let ω := (vDeg 1 0 T.1).toNat
  have hωpos : 0 < ω := by
    dsimp [ω]
    omega
  have hω : vDeg 1 0 T.1 = (ω : ℤ) := by
    dsimp [ω]
    omega
  have hhom : (leadingForm 1 0 T.1).IsWeightedHomogeneous
      (wt 1 0) (ω : ℤ) := by
    rw [← hω]
    change (MvPolynomial.weightedHomogeneousComponent
      (wt 1 0) (vDeg 1 0 T.1) (symbol T.1)).IsWeightedHomogeneous
        (wt 1 0) (vDeg 1 0 T.1)
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T.1) (w := wt 1 0) (n := vDeg 1 0 T.1)
  obtain ⟨U, hshape⟩ := horizontal_homogeneous_shape
    (leadingForm 1 0 T.1) ω hhom
  exact ⟨ω, U, hωpos, hω, hshape⟩

end Dixmier.Weyl
