/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutCoeffRecurrence

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First contraction in ramified normal ordering

For arbitrary derivative order `n` and Laurent coefficient `f`, the
normal-ordered expansion of `Y^n M_f` has top coefficient `f` and next
coefficient `n · f'`. These are the two terms needed for the endpoint
coefficient of a commutator. No cutoff on `n` or the Laurent support is used.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedDerivativePBWPower (l : ℕ)
    (f : LaurentPolynomial ℂ) : ℕ → (ℕ →₀ LaurentPolynomial ℂ)
  | 0 => Finsupp.single 0 f
  | n+1 => ramifiedDerivativeLeftLinear l (ramifiedDerivativePBWPower l f n)

theorem ramifiedDerivativePBWPower_eval (l : ℕ)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedNormalEval l (ramifiedDerivativePBWPower l f n) =
      (ramifiedDerivative l)^n * ramifiedCoeffMul f := by
  induction n with
  | zero =>
      simpa [ramifiedDerivativePBWPower, ramifiedNormalEvalLinear_apply]
        using ramifiedNormalEvalLinear_single l 0 f
  | succ n ih =>
      rw [ramifiedDerivativePBWPower,
        ramifiedNormalEval_derivative_left, ih, pow_succ']
      simp only [mul_assoc]

theorem ramifiedDerivativePBWPower_zero_above (l : ℕ)
    (f : LaurentPolynomial ℂ) (n j : ℕ) (hnj : n < j) :
    ramifiedDerivativePBWPower l f n j = 0 := by
  induction n generalizing j with
  | zero =>
      have hj : j ≠ 0 := by omega
      simp [ramifiedDerivativePBWPower, hj]
  | succ n ih =>
      rw [ramifiedDerivativePBWPower, ramifiedDerivativeLeftLinear_apply]
      have hj : j ≠ 0 := by omega
      have hprev : n < j - 1 := by omega
      have hcur : n < j := by omega
      simp [hj, ih (j-1) hprev, ih j hcur]

theorem ramifiedDerivativePBWPower_top (l : ℕ)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedDerivativePBWPower l f n n = f := by
  induction n with
  | zero => simp [ramifiedDerivativePBWPower]
  | succ n ih =>
      rw [ramifiedDerivativePBWPower, ramifiedDerivativeLeftLinear_apply]
      have hz := ramifiedDerivativePBWPower_zero_above l f n (n+1) (by omega)
      simp [ih, hz]

theorem ramifiedDerivativePBWPower_next (l : ℕ)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedDerivativePBWPower l f (n+1) n =
      (n+1 : ℂ) • ramifiedDerivative l f := by
  induction n with
  | zero =>
      simp [ramifiedDerivativePBWPower, ramifiedDerivativeLeftLinear_apply]
  | succ n ih =>
      rw [ramifiedDerivativePBWPower, ramifiedDerivativeLeftLinear_apply]
      have hprev : (n+1)-1 = n := by omega
      rw [hprev, ih, ramifiedDerivativePBWPower_top]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      norm_num [two_smul]

theorem ramifiedPBWCoeffs_derivativePow_coeff (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedYGen l)^n * ramifiedCoeffGen l f) =
        ramifiedDerivativePBWPower l f n := by
  apply ramifiedPBWCoeffs_eq_of_eval
  simpa [ramifiedYGen, ramifiedCoeffGen] using
    ramifiedDerivativePBWPower_eval l f n

theorem ramifiedPBWCoeffs_derivativePow_top (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedYGen l)^n * ramifiedCoeffGen l f) n = f := by
  rw [ramifiedPBWCoeffs_derivativePow_coeff,
    ramifiedDerivativePBWPower_top]

theorem ramifiedPBWCoeffs_derivativePow_next (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedYGen l)^(n+1) * ramifiedCoeffGen l f) n =
        (n+1 : ℂ) • ramifiedDerivative l f := by
  rw [ramifiedPBWCoeffs_derivativePow_coeff,
    ramifiedDerivativePBWPower_next]

end Dixmier.Weyl
