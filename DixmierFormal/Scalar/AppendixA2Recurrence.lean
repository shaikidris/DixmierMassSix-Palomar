/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.2: arbitrary-degree coefficient recurrence

The normalized differential equation yields the adjacent-coefficient
identity at every degree. Its first instance excludes `ρ-2s=1` when
the double-root factor has positive degree. Scaling and full-support
noncancellation remain separate obligations.
-/

namespace Dixmier
open Polynomial

private theorem coeff_X_derivative_succ (B : ℂ[X]) (n : ℕ) :
    (X * derivative B).coeff (n+1) = (n+1 : ℂ) * B.coeff (n+1) := by
  rw [coeff_X_mul, coeff_derivative]
  ring

private theorem coeff_X_sq_derivative_succ (B : ℂ[X]) (n : ℕ) :
    (X * (X * derivative B)).coeff (n+1) = (n : ℂ) * B.coeff n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [show n+1+1 = (n+1)+1 by omega, coeff_X_mul, coeff_X_mul,
        coeff_derivative]
      norm_cast
      ring

theorem appendix_A2_recurrence_raw {h : ℂ} {D : ℕ} {B : ℂ[X]}
    (heq : C h*X*(X-1)*derivative B - (C (h*(D : ℂ))*X-1)*B = 1) (n : ℕ) :
    (h*(n+1 : ℂ)-1)*B.coeff (n+1) = -h*((D : ℂ)-(n : ℂ))*B.coeff n := by
  have hc := congrArg (fun p : ℂ[X] => p.coeff (n+1)) heq
  -- Normalize polynomial products before extracting coefficients.
  have hrw : C h*X*(X-1)*derivative B - (C (h*(D : ℂ))*X-1)*B =
      C h*(X*(X*derivative B)) - C h*(X*derivative B) -
      C (h*(D : ℂ))*(X*B) + B := by ring
  rw [hrw] at hc
  simp only [coeff_sub, coeff_add, coeff_C_mul] at hc
  rw [coeff_X_sq_derivative_succ, coeff_X_derivative_succ,
    coeff_X_mul, coeff_one, if_neg (by omega : n+1 ≠ 0)] at hc
  ring_nf at hc ⊢
  linear_combination -hc

theorem appendix_A2_h_ne_one {D : ℕ} {B : ℂ[X]}
    (hD : 0 < D) (hB0 : B.eval 0 = 1)
    (heq : C (1 : ℂ)*X*(X-1)*derivative B -
      (C ((1 : ℂ)*(D : ℂ))*X-1)*B = 1) : False := by
  have hc := appendix_A2_recurrence_raw (h := (1 : ℂ)) (D := D) (B := B) heq 0
  have hc0 : B.coeff 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hB0
  rw [hc0] at hc
  norm_num at hc
  exact (Nat.cast_ne_zero.mpr (by omega : D ≠ 0)) hc

theorem appendix_A2_h_gt_one {ρ s : ℕ} {B : ℂ[X]}
    (hsρ : s < ρ) (hB0 : B.eval 0 = 1) (hD : 0 < B.natDegree)
    (hcomp : Comp ρ s (B^2) (B*(X-1))) : 2*s+1 < ρ := by
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hpos : 2*s < ρ := appendix_factor_h_pos ρ s (1 : ℂ[X]) B (X-1)
    hsρ one_ne_zero hB (by simpa only [C_1] using X_sub_C_ne_zero (1 : ℂ))
    hD (by simpa using hcomp)
  by_contra hn
  have hρ : ρ = 2*s+1 := by omega
  have hh : (ρ : ℂ)-2*(s : ℂ) = 1 := by
    rw [hρ]
    push_cast
    ring
  have heq := appendix_A2_equation_from_comp hsρ hB hD hcomp
  rw [hh] at heq
  exact appendix_A2_h_ne_one hD hB0 (by simpa using heq)

end Dixmier
