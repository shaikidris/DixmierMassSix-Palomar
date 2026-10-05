/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2Recurrence

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.2: alternating coefficients

For every degree up to `D`, the normalized recurrence with integer `h≥2`
forces a strictly positive real magnitude and sign `(-1)^n`. This proves
coefficient realness and nonvanishing without a degree search. The power
term-count consequence and general linear-factor scaling remain open.
-/

namespace Dixmier
open Polynomial

private theorem signed_step {a b x : ℝ} {n : ℕ} {z znext : ℂ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hz : z = (((-1 : ℝ)^n * x : ℝ) : ℂ))
    (hrec : (a : ℂ) * znext = -(b : ℂ)*z) :
    ∃ y : ℝ, 0 < y ∧ znext = (((-1 : ℝ)^(n+1) * y : ℝ) : ℂ) := by
  refine ⟨b/a*x, mul_pos (div_pos hb ha) hx, ?_⟩
  apply mul_left_cancel₀ (by exact_mod_cast (ne_of_gt ha) : (a : ℂ) ≠ 0)
  rw [hrec, hz]
  push_cast
  rw [pow_succ]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  field_simp [haC]

theorem appendix_A2_alternating_coefficients {h D : ℕ} {B : ℂ[X]}
    (hh : 2 ≤ h) (hB0 : B.eval 0 = 1)
    (heq : C (h : ℂ)*X*(X-1)*derivative B -
      (C ((h : ℂ)*(D : ℂ))*X-1)*B = 1) :
    ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      B.coeff n = (((-1 : ℝ)^n * x : ℝ) : ℂ) := by
  intro n hn
  induction n with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      simpa [coeff_zero_eq_eval_zero, hB0]
  | succ n ih =>
      have hnlt : n < D := by omega
      obtain ⟨x, hx, hxn⟩ := ih (by omega)
      let a : ℝ := (h : ℝ)*(n+1 : ℝ)-1
      let b : ℝ := (h : ℝ)*((D-n : ℕ) : ℝ)
      have ha : 0 < a := by
        dsimp [a]
        have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
        have hn' : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n+1)
        nlinarith
      have hb : 0 < b := by
        dsimp [b]
        have hh' : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
        have hn' : (0 : ℝ) < (D-n : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hnlt
        positivity
      have hrec := appendix_A2_recurrence_raw (h := (h : ℂ)) (D := D)
        (B := B) heq n
      have hrec' : (a : ℂ)*B.coeff (n+1) = -(b : ℂ)*B.coeff n := by
        dsimp [a,b]
        push_cast
        rw [Nat.cast_sub (le_of_lt hnlt)]
        convert hrec using 1 <;> ring
      exact signed_step ha hb hx hxn hrec'

end Dixmier
