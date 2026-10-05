/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedFaceCanonical
public import DixmierFormal.Weyl.GGVPairedFaceWeightRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Adjacent ordered entries carry the same pair weight ratio

This adapter removes the direction witnesses from the previous theorem.
It obtains the actual primitive normals directly from two consecutive
entries in the finite ordered slope list.
-/

namespace Dixmier.Weyl

/-- Consecutive entries of the actual ordered negative-face list have
one positive coprime ratio relating `P` and `Q` at both faces. -/
theorem counterexample_ordered_adjacent_common_weight_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length) :
    let t₁ := (ggvOrderedNegativeFaceSlopes P)[j]
    let t₂ := (ggvOrderedNegativeFaceSlopes P)[j+1]
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      vDeg (t₁.den : ℤ) t₁.num P.1 * (n : ℤ) =
        vDeg (t₁.den : ℤ) t₁.num Q.1 * (d : ℤ) ∧
      vDeg (t₂.den : ℤ) t₂.num P.1 * (n : ℤ) =
        vDeg (t₂.den : ℤ) t₂.num Q.1 * (d : ℤ) := by
  let t₁ := (ggvOrderedNegativeFaceSlopes P)[j]
  let t₂ := (ggvOrderedNegativeFaceSlopes P)[j+1]
  have hj₁ : j < (ggvOrderedNegativeFaceSlopes P).length := by omega
  have ht₁ : t₁ ∈ ggvOrderedNegativeFaceSlopes P :=
    List.getElem_mem hj₁
  have ht₂ : t₂ ∈ ggvOrderedNegativeFaceSlopes P :=
    List.getElem_mem hj
  obtain ⟨ρ₁, s₁, hρ₁, hs₁, hdir₁, hface₁, hslope₁, hρeq₁, hσeq₁⟩ :=
    ggv_ordered_negative_entry_nat_face P t₁ ht₁
  obtain ⟨ρ₂, s₂, _, hs₂, hdir₂, hface₂, hslope₂, hρeq₂, hσeq₂⟩ :=
    ggv_ordered_negative_entry_nat_face P t₂ ht₂
  obtain ⟨n, d, hn, hd, hcop, hweight₁, hweight₂⟩ :=
    counterexample_paired_successor_common_weight_ratio
      P Q hpair ρ₁ s₁ ρ₂ s₂ hρ₁ hs₁ hs₂ hdir₁ hdir₂
      j hj hslope₁ hslope₂ hface₁ hface₂
  refine ⟨n, d, hn, hd, hcop, ?_, ?_⟩
  · simpa only [hρeq₁, hσeq₁] using hweight₁
  · simpa only [hρeq₂, hσeq₂] using hweight₂

end Dixmier.Weyl
