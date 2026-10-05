/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutRecurrence

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Coefficientwise recurrence for the ramified shear

The finite PBW update has a local formula at each derivative order.
This is the form needed for an induction on Newton support.
-/
namespace Dixmier.Weyl

theorem ramifiedDerivativeLeftLinear_apply (l : ℕ)
    (a : ℕ →₀ LaurentPolynomial ℂ) (j : ℕ) :
    (ramifiedDerivativeLeftLinear l a) j =
      (if j = 0 then 0 else a (j-1)) + ramifiedDerivative l (a j) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero =>
      simp
  | add a b ha hb =>
      rw [map_add, Finsupp.add_apply, ha, hb]
      simp only [Finsupp.add_apply, map_add]
      split_ifs <;> abel
  | single k f =>
      rw [ramifiedDerivativeLeftLinear_single, Finsupp.add_apply]
      by_cases hj : j = 0
      · subst j
        by_cases hk0 : k = 0
        · subst k
          simp
        · simp [hk0]
      · by_cases hk : j = k + 1
        · subst j
          simp
        · by_cases hkj : j = k
          · subst j
            have hkpred : k ≠ k - 1 := by omega
            simp [hj, hkpred]
          · have hkpred : k ≠ j - 1 := by omega
            simp [hj, hk, hkj, hkpred]

theorem ramifiedCoeffLeftLinear_apply (h : LaurentPolynomial ℂ)
    (a : ℕ →₀ LaurentPolynomial ℂ) (j : ℕ) :
    (ramifiedCoeffLeftLinear h a) j = h * a j := by
  rfl

/-- Exact local recurrence for every PBW coefficient after one
left multiplication by `Y+h`. -/
theorem ramifiedShiftPBWStep_apply (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ)
    (j : ℕ) :
    (ramifiedShiftPBWStep l h a) j =
      (if j = 0 then 0 else a (j-1)) +
        ramifiedDerivative l (a j) + h * a j := by
  rw [ramifiedShiftPBWStep, Finsupp.add_apply,
    ramifiedDerivativeLeftLinear_apply,
    ramifiedCoeffLeftLinear_apply]

/-- Every shifted power has PBW derivative order at most its exponent. -/
theorem ramifiedShiftPBWPower_zero_above (l : ℕ)
    (h : LaurentPolynomial ℂ) (n j : ℕ) (hjn : n < j) :
    (ramifiedShiftPBWPower l h n) j = 0 := by
  induction n generalizing j with
  | zero =>
      have hj : j ≠ 0 := by omega
      simp [ramifiedShiftPBWPower, hj]
  | succ n ih =>
      rw [ramifiedShiftPBWPower, ramifiedShiftPBWStep_apply]
      have hj : j ≠ 0 := by omega
      have hp : n < j - 1 := by omega
      have hq : n < j := by omega
      simp [hj, ih (j-1) hp, ih j hq]

/-- The coefficient of `Y^n` in `(Y+h)^n` is exactly one. -/
theorem ramifiedShiftPBWPower_top (l : ℕ)
    (h : LaurentPolynomial ℂ) (n : ℕ) :
    (ramifiedShiftPBWPower l h n) n = 1 := by
  induction n with
  | zero =>
      simp [ramifiedShiftPBWPower]
  | succ n ih =>
      rw [ramifiedShiftPBWPower, ramifiedShiftPBWStep_apply]
      have hz := ramifiedShiftPBWPower_zero_above l h n (n+1) (by omega)
      simp [hz, ih]

/-- The canonical derivative order of every shifted power is its
exponent, without a cutoff on the exponent or on `h`. -/
theorem ramifiedShiftedYGen_order (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedPBWOrder l hl ((ramifiedShiftedYGen l h)^n) = n := by
  rw [ramifiedPBWOrder, ramifiedShiftPBWPower_canonical]
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    change j ≤ n
    by_contra hbad
    have hz := ramifiedShiftPBWPower_zero_above l h n j (by omega)
    exact (Finsupp.mem_support_iff.mp hj) hz
  · apply Finset.le_sup (f := id)
    exact Finsupp.mem_support_iff.mpr
      (by rw [ramifiedShiftPBWPower_top]; exact one_ne_zero)

end Dixmier.Weyl
