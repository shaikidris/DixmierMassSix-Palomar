/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.MateDescent
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Nat.Prime.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Integer parameters of the pure-power face

The paper's face exclusion assumes `(q-1)ρ = q s + 1`.  The consequences here
are independent of the Newton-cut theorems and will be reused when their exact
hypotheses are assembled.
-/

namespace Dixmier.Weyl

theorem purePower_rho_pos {q s ρ : ℕ} (_hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) : 0 < ρ := by
  by_contra hρ
  have hz : ρ = 0 := Nat.eq_zero_of_not_pos hρ
  simp [hz] at h

theorem purePower_s_lt_rho {q s ρ : ℕ} (hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) : s < ρ := by
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hρ := purePower_rho_pos hq h
  have hsplit : q * ρ = (q - 1) * ρ + ρ := by
    calc
      q * ρ = ((q - 1) + 1) * ρ := by rw [hq1]
      _ = (q - 1) * ρ + ρ := by ring
  rw [h] at hsplit
  by_contra hs
  have hle : ρ ≤ s := Nat.le_of_not_gt hs
  have hmul : q * ρ ≤ q * s := Nat.mul_le_mul_left q hle
  omega

/-- At the horizontal boundary, the pure-power parameter identity forces the
unique integral values `q=2` and `ρ=1`. -/
theorem purePower_horizontal_parameters {q ρ : ℕ} (hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * 0 + 1) : q = 2 ∧ ρ = 1 := by
  have hprod : (q - 1) * ρ = 1 := by simpa using h
  have hdq : q - 1 ∣ 1 := ⟨ρ, hprod.symm⟩
  have hdr : ρ ∣ 1 := ⟨q - 1, by simpa only [mul_comm] using hprod.symm⟩
  have hq1 := Nat.dvd_one.mp hdq
  have hρ1 := Nat.dvd_one.mp hdr
  omega

theorem purePower_coprime {q s ρ : ℕ} (_hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) : Nat.Coprime ρ s := by
  let d := Nat.gcd ρ s
  have hdρ : d ∣ ρ := Nat.gcd_dvd_left ρ s
  have hds : d ∣ s := Nat.gcd_dvd_right ρ s
  have hleft : d ∣ (q - 1) * ρ := dvd_mul_of_dvd_right hdρ _
  have hright : d ∣ q * s := dvd_mul_of_dvd_right hds _
  rw [h] at hleft
  have h1 : d ∣ 1 := (Nat.dvd_add_iff_right hright).mpr hleft
  exact Nat.dvd_one.mp h1

/-- The pure-power parameter identity supplies the primitive positive-sum
direction required by the GGV cut and companion interfaces. -/
theorem purePower_isDirection {q s ρ : ℕ} (hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) :
    IsDirection ρ (-(s : ℤ)) := by
  have hcoprime := purePower_coprime hq h
  have hsρ := purePower_s_lt_rho hq h
  constructor
  · simpa [Int.gcd, Nat.Coprime] using hcoprime
  · omega

theorem purePower_weight_identity {q s ρ : ℕ} (hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) :
    (q : ℤ) * ((ρ : ℤ) - s) = ρ + 1 := by
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hi : ((q - 1 : ℕ) : ℤ) * ρ = (q : ℤ) * s + 1 := by exact_mod_cast h
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 :=
    Nat.cast_sub (by omega : 1 ≤ q)
  rw [hqcast] at hi
  nlinarith

theorem purePower_normalized_corner {q s ρ : ℕ} (hq : 2 ≤ q)
    (h : (q - 1) * ρ = q * s + 1) :
    (1 : ℚ) + (q : ℚ) * s / ρ = q - 1 / ρ := by
  have hρ := purePower_rho_pos hq h
  have hρq : (ρ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hρ)
  have hi : ((q - 1 : ℕ) : ℚ) * ρ = (q : ℚ) * s + 1 := by exact_mod_cast h
  have hq1 : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 :=
    Nat.cast_sub (by omega : 1 ≤ q)
  rw [hq1] at hi
  field_simp [hρq]
  nlinarith [hi]

/-- Primality turns the surviving condition `p ∤ j` into a reduced ratio. -/
theorem primeMateExponent_coprime {p j : ℕ} (hp : p.Prime) (hnot : ¬ p ∣ j) :
    Nat.Coprime j p :=
  (hp.coprime_iff_not_dvd.mpr hnot).symm

/-- The two weight ratios needed by the cut theorem are nonintegral.  The
common positive factor `ρ` cancels exactly; no mate-order bound is used. -/
theorem primeMateWeights_nonintegral {p j ρ : ℕ} (hp : p.Prime)
    (hj : 1 < j) (hρ : 0 < ρ) (hnot : ¬ p ∣ j) :
    ¬ p * ρ ∣ j * ρ ∧ ¬ j * ρ ∣ p * ρ := by
  constructor
  · intro hdiv
    exact hnot ((Nat.mul_dvd_mul_iff_right hρ).mp hdiv)
  · intro hdiv
    have hjp : j ∣ p := (Nat.mul_dvd_mul_iff_right hρ).mp hdiv
    have hjne : j ≠ 1 := by omega
    have heq : p = j := (Nat.Prime.dvd_iff_eq hp hjne).mp hjp
    subst j
    exact hnot (dvd_refl p)

/-- Cancellation of the common face-weight factor gives the exact rational
ratio used to identify the denominator after coprimality is established. -/
theorem primeMateWeight_ratio {p j ρ : ℕ} (hp : p.Prime) (hρ : 0 < ρ) :
    ((j * ρ : ℕ) : ℚ) / ((p * ρ : ℕ) : ℚ) = (j : ℚ) / (p : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hρq : (ρ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hρ)
  simp only [Nat.cast_mul]
  field_simp [hpq, hρq]

/-- The same two exclusions in the signed-weight type required by the
published cut interface. -/
theorem primeMateWeights_nonintegral_int {p j ρ : ℕ} (hp : p.Prime)
    (hj : 1 < j) (hρ : 0 < ρ) (hnot : ¬ p ∣ j) :
    ¬ ((p : ℤ) * ρ ∣ (j : ℤ) * ρ) ∧
      ¬ ((j : ℤ) * ρ ∣ (p : ℤ) * ρ) := by
  obtain ⟨hforward, hbackward⟩ := primeMateWeights_nonintegral hp hj hρ hnot
  constructor
  · intro hdiv
    apply hforward
    exact_mod_cast hdiv
  · intro hdiv
    apply hbackward
    exact_mod_cast hdiv

end Dixmier.Weyl
