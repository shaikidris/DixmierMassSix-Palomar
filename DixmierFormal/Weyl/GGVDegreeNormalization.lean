/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Coprime normalization of the two total degrees

This is the arithmetic step in G13 Section 7 that writes the degrees of a
standard minimal pair as coprime outer exponents times their degree gcd.
-/

namespace Dixmier.Weyl

/-- A coprime integer ratio determines the common gcd factor of two degrees. -/
theorem coprime_degree_ratio_normalization
    (a b m n : ℕ) (hm : 0 < m) (hcop : Nat.Coprime m n)
    (hratio : a * n = b * m) :
    a = m * Nat.gcd a b ∧ b = n * Nat.gcd a b := by
  have hmdvd : m ∣ a := by
    apply hcop.dvd_of_dvd_mul_right
    rw [mul_comm]
    exact ⟨b, (mul_comm n a).trans (hratio.trans (mul_comm b m))⟩
  let k := a / m
  have ha : a = m * k := by
    exact (Nat.div_mul_cancel hmdvd).symm.trans (mul_comm _ _)
  have hb : b = n * k := by
    rw [ha] at hratio
    apply Nat.eq_of_mul_eq_mul_left hm
    calc
      m * b = b * m := by ring
      _ = (m * k) * n := hratio.symm
      _ = m * (n * k) := by ring
  have hgcd : Nat.gcd a b = k := by
    rw [ha, hb, Nat.gcd_mul_right]
    rw [show Nat.gcd m n = 1 from hcop]
    omega
  rw [hgcd]
  exact ⟨ha, hb⟩

end Dixmier.Weyl
