/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Rescaling the variable

Substitution `w ↦ c w` for `c ≠ 0`: coefficients scale by `cⁿ`, supports and term counts are
unchanged, roots are divided by `c`, and the substitution is undone by `w ↦ c⁻¹ w`.
-/

namespace Dixmier

open Polynomial

variable {K : Type*} [Field K]

theorem coeff_comp_C_mul_X (p : K[X]) (c : K) (n : ℕ) :
    (p.comp (C c * X)).coeff n = p.coeff n * c ^ n := comp_C_mul_X_coeff

theorem support_comp_C_mul_X {p : K[X]} {c : K} (hc : c ≠ 0) :
    (p.comp (C c * X)).support = p.support := by
  ext n; simp [mem_support_iff, comp_C_mul_X_coeff, hc]

theorem termCount_comp_C_mul_X {p : K[X]} {c : K} (hc : c ≠ 0) :
    termCount (p.comp (C c * X)) = termCount p := by
  unfold termCount; rw [support_comp_C_mul_X hc]

theorem comp_C_mul_X_comp_C_inv_mul_X (p : K[X]) {c : K} (hc : c ≠ 0) :
    (p.comp (C c * X)).comp (C c⁻¹ * X) = p := by
  rw [comp_assoc]
  have : (C c * X).comp (C c⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  rw [this, comp_X]

theorem X_sub_C_comp_C_mul_X {c a : K} (hc : c ≠ 0) :
    (X - C a).comp (C c * X) = C c * (X - C (a / c)) := by
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ hc]

theorem pow_dvd_comp_C_mul_X {S : K[X]} {a c : K} (hc : c ≠ 0) {m : ℕ}
    (h : (X - C a) ^ m ∣ S) : (X - C (a / c)) ^ m ∣ S.comp (C c * X) := by
  obtain ⟨q, rfl⟩ := h
  rw [mul_comp, pow_comp, X_sub_C_comp_C_mul_X hc, mul_pow]
  exact ⟨C c ^ m * q.comp (C c * X), by ring⟩

theorem natDegree_comp_C_mul_X {p : K[X]} {c : K} (hc : c ≠ 0) :
    (p.comp (C c * X)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X c hc, mul_one]

theorem eval_zero_comp_C_mul_X (p : K[X]) (c : K) : (p.comp (C c * X)).eval 0 = p.eval 0 := by
  simp [eval_comp]

end Dixmier
