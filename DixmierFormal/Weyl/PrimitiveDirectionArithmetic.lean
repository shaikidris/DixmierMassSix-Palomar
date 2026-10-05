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
# Recovering a primitive direction from an integral perpendicular vector
-/

namespace Dixmier.Weyl

/-- A primitive positive direction is recovered from any nonzero positive
integer vector perpendicular to it. -/
theorem primitive_direction_of_weight_line
    (ρ s a b : ℕ) (hρ : 0 < ρ)
    (haPos : 0 < a) (hcop : Nat.Coprime ρ s) (hline : ρ * a = s * b) :
    ρ = b / Nat.gcd a b ∧ s = a / Nat.gcd a b := by
  have hρdvd : ρ ∣ b := by
    apply hcop.dvd_of_dvd_mul_right
    rw [mul_comm]
    exact ⟨a, hline.symm⟩
  let k := b / ρ
  have hb : b = ρ * k := by
    exact (Nat.div_mul_cancel hρdvd).symm.trans (mul_comm _ _)
  have hkpos : 0 < k := by
    have hleft : 0 < ρ * a := mul_pos hρ haPos
    have hright : 0 < s * b := hline.symm ▸ hleft
    have hbpos : 0 < b := by
      by_contra hn
      have hbzero : b = 0 := by omega
      simp [hbzero] at hright
    exact Nat.div_pos (Nat.le_of_dvd hbpos hρdvd) hρ
  have ha : a = s * k := by
    rw [hb] at hline
    apply Nat.eq_of_mul_eq_mul_left hρ
    calc
      ρ * a = s * (ρ * k) := hline
      _ = ρ * (s * k) := by ring
  have hgcd : Nat.gcd a b = k := by
    rw [ha, hb, Nat.gcd_mul_right]
    rw [Nat.gcd_comm, show Nat.gcd ρ s = 1 from hcop]
    omega
  rw [hgcd, ha, hb]
  constructor
  · rw [mul_comm ρ k, Nat.mul_div_cancel_left ρ hkpos]
  · rw [mul_comm s k, Nat.mul_div_cancel_left s hkpos]

end Dixmier.Weyl
