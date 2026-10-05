/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Companion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Lowest-order obstruction for a diagonal companion face

The leading derivative-bracket equation cannot hold if the first
nonzero coefficient of its right-hand side occurs at order `m > 0`
and the two scalar weights satisfy `α = β m`.
-/

namespace Dixmier.General
open Polynomial

theorem diagonal_lowest_order_bracket_ne
    (f g : ℂ[X]) (α β : ℂ) (m : ℕ)
    (hm : 0 < m) (hβ : β ≠ 0)
    (hfirst : g.coeff m ≠ 0)
    (hlow : ∀ j < m, g.coeff j = 0)
    (hdiag : α = β * (m : ℂ)) :
    C α * derivative f * g - C β * f * derivative g ≠ g := by
  intro heq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨q,hq⟩ : X ^ (k+1) ∣ g :=
    X_pow_dvd_iff.mpr hlow
  have hq0 : q.coeff 0 ≠ 0 := by
    have hc : g.coeff (k+1) = q.coeff 0 := by
      rw [hq]
      simpa only [Nat.zero_add] using coeff_X_pow_mul q (k+1) 0
    rw [hc] at hfirst
    simpa only [Nat.succ_eq_add_one] using hfirst
  have hred :
      C α * X * derivative f * q -
        C β * (C ((k+1 : ℕ) : ℂ) * f * q +
          X * f * derivative q) = X * q := by
    have hfac :
        X^k * (C α * X * derivative f * q -
          C β * (C ((k+1 : ℕ) : ℂ) * f * q +
            X * f * derivative q)) = X^k * (X * q) := by
      rw [hq] at heq
      calc
        X^k * (C α * X * derivative f * q -
          C β * (C ((k+1 : ℕ) : ℂ) * f * q +
            X * f * derivative q)) =
            C α * derivative f * (X^(k+1) * q) -
              C β * f * derivative (X^(k+1) * q) := by
                rw [derivative_mul, derivative_X_pow]
                simp only [show k + 1 - 1 = k by omega]
                ring
        _ = X^k * (X * q) := by rw [heq]; ring
    exact (mul_left_cancel₀ (pow_ne_zero k X_ne_zero) hfac)
  have hf0 : f.coeff 0 = 0 := by
    have h0 := congrArg (Polynomial.eval (0 : ℂ)) hred
    simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X,
      mul_zero, zero_mul, add_zero] at h0
    have hq0' : q.eval 0 ≠ 0 := by
      simpa [coeff_zero_eq_eval_zero] using hq0
    have hmC : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k+1 ≠ 0)
    have hf0' : f.eval 0 = 0 := by
      have hprod : β * ((k+1 : ℕ) : ℂ) * f.eval 0 * q.eval 0 = 0 := by
        linear_combination -h0
      exact (mul_eq_zero.mp (mul_eq_zero.mp hprod |>.resolve_right hq0')).resolve_left
        (mul_ne_zero hβ hmC)
    simpa [coeff_zero_eq_eval_zero] using hf0'
  obtain ⟨t,ht⟩ : X ∣ f := X_dvd_iff.mpr hf0
  have hred2 :
      C α * (t + X * derivative t) * q -
        C β * (C ((k+1 : ℕ) : ℂ) * t * q +
          X * t * derivative q) = q := by
    have hfac : X * (C α * (t + X * derivative t) * q -
        C β * (C ((k+1 : ℕ) : ℂ) * t * q +
          X * t * derivative q)) = X * q := by
      rw [ht] at hred
      calc
        X * (C α * (t + X * derivative t) * q -
          C β * (C ((k+1 : ℕ) : ℂ) * t * q +
            X * t * derivative q)) =
          C α * X * derivative (X * t) * q -
            C β * (C ((k+1 : ℕ) : ℂ) * (X * t) * q +
              X * (X * t) * derivative q) := by
                rw [derivative_mul, derivative_X]
                ring
        _ = X * q := hred
    exact mul_left_cancel₀ X_ne_zero hfac
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) hred2
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X,
    zero_mul, add_zero] at h0
  have hq0' : q.eval 0 ≠ 0 := by
    simpa [coeff_zero_eq_eval_zero] using hq0
  have hα : α = β * ((k+1 : ℕ) : ℂ) := by simpa using hdiag
  rw [hα] at h0
  exact hq0' (by linear_combination -h0)

end Dixmier.General
