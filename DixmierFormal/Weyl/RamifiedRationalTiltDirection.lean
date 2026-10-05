/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FiniteSupportAdjacentDirection

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# An integral Newton direction for a rational downward tilt

The finite-support first-slope construction returns a rational tilt.
Multiplying by the positive denominator and the ramification index
turns its supporting functional into an integral Newton weight.
-/

namespace Dixmier.Weyl

def rationalTiltRho (l : ℕ) (ρ : ℤ) (t : ℚ) : ℤ :=
  ρ * (l : ℤ) * (t.den : ℤ)

def rationalTiltSigma (l : ℕ) (σ : ℤ) (t : ℚ) : ℤ :=
  σ * (l : ℤ) * (t.den : ℤ) - t.num

theorem rationalTilt_weight_scale
    (l : ℕ) (ρ σ : ℤ) (t : ℚ) (p : ℤ × ℕ) :
    ((ramifiedWeight l (rationalTiltRho l ρ t)
      (rationalTiltSigma l σ t) p : ℤ) : ℚ) =
      (l : ℚ) * (t.den : ℚ) *
        (((ramifiedWeight l ρ σ p : ℤ) : ℚ) - t * (p.2 : ℚ)) := by
  have hd : (t.den : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero t
  have hnum : t * (t.den : ℚ) = (t.num : ℚ) := by
    calc
      t * (t.den : ℚ) =
          ((t.num : ℚ) / (t.den : ℚ)) * (t.den : ℚ) := by
            rw [Rat.num_div_den]
      _ = (t.num : ℚ) := by field_simp
  dsimp [ramifiedWeight, rationalTiltRho, rationalTiltSigma]
  push_cast
  rw [← hnum]
  ring

theorem rationalTilt_rho_pos
    (l : ℕ) (hl : 0 < l) (ρ : ℤ) (hρ : 0 < ρ) (t : ℚ) :
    0 < rationalTiltRho l ρ t := by
  dsimp [rationalTiltRho]
  exact mul_pos (mul_pos hρ (by exact_mod_cast hl))
    (by exact_mod_cast Rat.den_pos t)

theorem rationalTilt_sum_pos
    (l : ℕ) (ρ σ : ℤ) (t : ℚ)
    (ht : t < (l : ℚ) * ((ρ+σ : ℤ) : ℚ)) :
    0 < rationalTiltRho l ρ t + rationalTiltSigma l σ t := by
  have hd : (0 : ℚ) < (t.den : ℚ) := by
    exact_mod_cast Rat.den_pos t
  have hnum : t * (t.den : ℚ) = (t.num : ℚ) := by
    calc
      t * (t.den : ℚ) =
          ((t.num : ℚ) / (t.den : ℚ)) * (t.den : ℚ) := by
            rw [Rat.num_div_den]
      _ = (t.num : ℚ) := by field_simp
  have hmul := mul_lt_mul_of_pos_right ht hd
  rw [hnum] at hmul
  have hq : (0 : ℚ) <
      ((l : ℚ) * ((ρ+σ : ℤ) : ℚ)) * (t.den : ℚ) - (t.num : ℚ) := by
    linarith
  have hz : (0 : ℤ) <
      (l : ℤ) * (ρ+σ) * (t.den : ℤ) - t.num := by
    exact_mod_cast hq
  dsimp [rationalTiltRho, rationalTiltSigma]
  nlinarith [hz]

theorem rationalTilt_support_bound
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (t : ℚ)
    (S : Finset (ℤ × ℕ)) (E : ℤ × ℕ)
    (hbound : ∀ p ∈ S,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - t * (p.2 : ℚ) ≤
        ((ramifiedWeight l ρ σ E : ℤ) : ℚ) - t * (E.2 : ℚ)) :
    ∀ p ∈ S,
      ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) p ≤
      ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) E := by
  have hscale : (0 : ℚ) < (l : ℚ) * (t.den : ℚ) :=
    mul_pos (by exact_mod_cast hl) (by exact_mod_cast Rat.den_pos t)
  intro p hp
  have hq := mul_le_mul_of_nonneg_left (hbound p hp) (le_of_lt hscale)
  rw [← rationalTilt_weight_scale, ← rationalTilt_weight_scale] at hq
  exact_mod_cast hq

/-- Before a finite support's own first slope, the integer direction
corresponding to an earlier rational tilt exposes only its old
endpoint. This is the singleton-mate-face interface needed by the
exact unequal-face exclusion. -/
theorem rationalTilt_before_first_slope_singleton
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (S : Finset (ℤ × ℕ)) (V : ℤ) (F : ℤ × ℕ)
    (t tFirst : ℚ) (ht : 0 < t) (hbefore : t < tFirst)
    (hF : ramifiedWeight l ρ σ F = V)
    (htop : ∀ p ∈ S, ramifiedWeight l ρ σ p ≤ V)
    (hfirst : ∀ p ∈ S,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (F.2 : ℚ))
    (p : ℤ × ℕ) (hp : p ∈ S)
    (hnew : ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) p =
      ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) F) :
    p = F := by
  have hscale : (0 : ℚ) < (l : ℚ) * (t.den : ℚ) :=
    mul_pos (by exact_mod_cast hl) (by exact_mod_cast Rat.den_pos t)
  have hnewQ := congrArg (fun z : ℤ => (z : ℚ)) hnew
  rw [rationalTilt_weight_scale, rationalTilt_weight_scale] at hnewQ
  have htie : ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - t * (p.2 : ℚ) =
      (V : ℚ) - t * (F.2 : ℚ) := by
    rw [← hF]
    exact (mul_left_cancel₀ (ne_of_gt hscale)) hnewQ
  exact ramifiedSupport_before_first_slope_singleton
    l ρ σ hρ S V F hF t tFirst ht hbefore htop hfirst p hp htie

end Dixmier.Weyl
