/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutSetup

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite normal-ordering recurrence for ramified shears

Left multiplication by `Y+h` sends a finite PBW sequence through a
derivative step and a coefficient step. Iterating this recurrence gives
an exact normal-ordered expansion at every power. The next Newton task
is a uniform support and leading-weight theorem for these coefficients.
-/
namespace Dixmier.Weyl

/-- The exact finite-PBW update for left multiplication by `Y+h`. -/
noncomputable def ramifiedShiftPBWStep (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ℕ →₀ LaurentPolynomial ℂ :=
  ramifiedDerivativeLeftLinear l a + ramifiedCoeffLeftLinear h a

theorem ramifiedNormalEval_shift_step (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedNormalEval l (ramifiedShiftPBWStep l h a) =
      ramifiedShiftedY l h * ramifiedNormalEval l a := by
  rw [ramifiedShiftPBWStep, ← ramifiedNormalEvalLinear_apply,
    map_add, ramifiedNormalEvalLinear_apply,
    ramifiedNormalEvalLinear_apply,
    ramifiedNormalEval_derivative_left,
    ramifiedNormalEval_coeff_left]
  exact (add_mul (ramifiedDerivative l) (ramifiedCoeffMul h)
    (ramifiedNormalEval l a)).symm

/-- The canonical recurrence producing the finite normal-ordered
coefficients of `(Y+h)^n`. -/
noncomputable def ramifiedShiftPBWPower (l : ℕ)
    (h : LaurentPolynomial ℂ) : ℕ → (ℕ →₀ LaurentPolynomial ℂ)
  | 0 => Finsupp.single 0 1
  | n+1 => ramifiedShiftPBWStep l h (ramifiedShiftPBWPower l h n)

theorem ramifiedShiftPBWPower_eval (l : ℕ)
    (h : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedNormalEval l (ramifiedShiftPBWPower l h n) =
      (ramifiedShiftedY l h)^n := by
  induction n with
  | zero =>
      simpa [ramifiedShiftPBWPower, ramifiedNormalEvalLinear_apply,
        ramifiedCoeffMul_one] using
        ramifiedNormalEvalLinear_single l 0 (1 : LaurentPolynomial ℂ)
  | succ n ih =>
      rw [ramifiedShiftPBWPower,
        ramifiedNormalEval_shift_step, ih, pow_succ']

theorem ramifiedShiftPBWPower_canonical (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (n : ℕ) :
    ramifiedPBWCoeffs l hl ((ramifiedShiftedYGen l h)^n) =
      ramifiedShiftPBWPower l h n := by
  apply ramifiedPBWCoeffs_eq_of_eval
  exact ramifiedShiftPBWPower_eval l h n

end Dixmier.Weyl
