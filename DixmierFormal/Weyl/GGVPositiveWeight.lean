/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedScalarNormalize

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positive weight of a counterexample member

GGV Proposition 1.4 supplies positivity before their preliminary companion
theorem. Opposite grades give this directly for every direction of positive
sum: choose the positive grade if `ρ > 0`, and the negative grade otherwise.
-/

namespace Dixmier.Weyl

open MvPolynomial

private theorem weight_le_vDeg_of_mem
    (T : A1 ℂ) (ρ σ : ℤ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (symbol T.1).support) :
    Finsupp.weight (wt ρ σ) d ≤ vDeg ρ σ T.1 := by
  have hbound : (Finsupp.weight (wt ρ σ) d : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T.1) := by
    change (Finsupp.weight (wt ρ σ) d : WithBot ℤ) ≤
      (symbol T.1).support.sup
        (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
    exact Finset.le_sup (f := fun e =>
      (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hd
  exact WithBot.le_unbotD (a := 0) hbound

/-- GGV's positive-weight prerequisite, derived from the formalized
opposite-grades theorem for every direction of positive sum. -/
theorem counterexample_vDeg_pos_all_directions
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) :
    0 < vDeg ρ σ P.1 := by
  obtain ⟨hplus, hminus⟩ := ggv_grades_opposite_proved P Q hpair
  by_cases hρ : 0 < ρ
  · obtain ⟨d, hd, hgrade⟩ := hplus
    have hw : 0 < Finsupp.weight (wt ρ σ) d := by
      obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
      rw [expo_weight]
      have hgd : 0 < (i : ℤ) - j := by simpa [grade, expo] using hgrade
      have h1 : 0 < ρ * ((i : ℤ) - j) := mul_pos hρ hgd
      have h2 : 0 ≤ (j : ℤ) * (ρ + σ) :=
        mul_nonneg (by exact_mod_cast Nat.zero_le j) (le_of_lt hdir.2)
      nlinarith
    exact lt_of_lt_of_le hw (weight_le_vDeg_of_mem P ρ σ d hd)
  · obtain ⟨d, hd, hgrade⟩ := hminus
    have hw : 0 < Finsupp.weight (wt ρ σ) d := by
      obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
      rw [expo_weight]
      have hgd : (i : ℤ) - j < 0 := by simpa [grade, expo] using hgrade
      have hσ : 0 < σ := by have hs := hdir.2; omega
      have h1 : 0 < σ * ((j : ℤ) - i) := mul_pos hσ (by omega)
      have h2 : 0 ≤ (i : ℤ) * (ρ + σ) :=
        mul_nonneg (by exact_mod_cast Nat.zero_le i) (le_of_lt hdir.2)
      nlinarith
    exact lt_of_lt_of_le hw (weight_le_vDeg_of_mem P ρ σ d hd)

end Dixmier.Weyl
