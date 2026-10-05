/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVNegativeHorizontalBoundary
public import DixmierFormal.Weyl.GGVPairedEndpointRatio
public import DixmierFormal.Weyl.GGVPairedFaceWeightRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The exact-pair weight ratio reaches the horizontal boundary

The last strict-negative face has a maximum-order point that remains on
the horizontal face. Applying this to both operators makes the points
proportional on the old face, and therefore transfers the same ratio to
the horizontal weights.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The two members have proportional occupied vertices shared by the
last strict-negative face and the horizontal face. -/
theorem counterexample_paired_last_negative_meets_horizontal
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j + 1 = (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] =
      (-(s : ℤ) : ℚ) / ρ)
    (hface : InDir (ρ : ℤ) (-(s : ℤ)) P.1) :
    ∃ (a b : Fin 2 →₀ ℕ) (n d : ℕ),
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      a ∈ (leadingForm 1 0 P.1).support ∧
      b ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) Q.1).support ∧
      b ∈ (leadingForm 1 0 Q.1).support ∧
      0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      n * a 0 = d * b 0 ∧ n * a 1 = d * b 1 := by
  obtain ⟨a, haN, haH, haMax⟩ :=
    counterexample_last_negative_face_meets_horizontal
      P Q hpair ρ s hρ hs hdir j hj hentry hface
  have hfaceQ : InDir (ρ : ℤ) (-(s : ℤ)) Q.1 :=
    (counterexample_strict_negative_InDir_iff P Q hpair
      ρ (-(s : ℤ)) hdir (by omega)).mp hface
  have hlist : ggvOrderedNegativeFaceSlopes P =
      ggvOrderedNegativeFaceSlopes Q :=
    ggv_ordered_negative_slopes_eq P Q hpair
  have hjQ : j + 1 = (ggvOrderedNegativeFaceSlopes Q).length := by
    rw [← hlist]
    exact hj
  have hentryQ : (ggvOrderedNegativeFaceSlopes Q)[j] =
      (-(s : ℤ) : ℚ) / ρ := by
    simpa only [← hlist] using hentry
  obtain ⟨b, hbN, hbH, hbMax⟩ :=
    counterexample_last_negative_face_meets_horizontal
      Q (-P) (isCounterexamplePair_swap_neg P Q hpair) ρ s hρ hs hdir
      j hjQ hentryQ hfaceQ
  obtain ⟨n, d, hn, hd, hcop, hx, hy⟩ :=
    counterexample_negative_face_maxima_proportional
      P Q hpair ρ s hρ hs hdir haN hbN haMax hbMax
  exact ⟨a, b, n, d, haN, haH, hbN, hbH, hn, hd, hcop, hx, hy⟩

/-- The reduced ratio on the last strict-negative face also relates
the two horizontal leading weights. -/
theorem counterexample_last_negative_horizontal_common_weight_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j + 1 = (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] =
      (-(s : ℤ) : ℚ) / ρ)
    (hface : InDir (ρ : ℤ) (-(s : ℤ)) P.1) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 * (n : ℤ) =
        vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (d : ℤ) ∧
      vDeg 1 0 P.1 * (n : ℤ) = vDeg 1 0 Q.1 * (d : ℤ) := by
  obtain ⟨a, b, n, d, haN, haH, hbN, hbH, hn, hd, hcop, hx, hy⟩ :=
    counterexample_paired_last_negative_meets_horizontal
      P Q hpair ρ s hρ hs hdir j hj hentry hface
  obtain ⟨hN, hH⟩ := paired_face_points_common_weight_ratio
    P Q (ρ : ℤ) (-(s : ℤ)) 1 0 a b n d haN haH hbN hbH hx hy
  exact ⟨n, d, hn, hd, hcop, hN, hH⟩

end Dixmier.Weyl
