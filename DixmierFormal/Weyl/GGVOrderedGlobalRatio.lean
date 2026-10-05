/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedFaceWeightRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Constant mate-to-source ratio on all actual negative faces

The exact-pair weighted-degree ratio agrees on neighboring members of
the finite ordered negative-face list. Induction carries this equality
across the entire list. The diagonal and horizontal boundary faces are
not members of this list and remain separate obligations.
-/

namespace Dixmier.Weyl

/-- The ratio of the mate's and source's actual weights in the
canonical primitive normal of a rational slope. -/
noncomputable def ggvNegativeFacePairRatio (P Q : A1 ℂ) (t : ℚ) : ℚ :=
  (vDeg (t.den : ℤ) t.num Q.1 : ℚ) /
    (vDeg (t.den : ℤ) t.num P.1 : ℚ)

/-- The ratio is identical at neighboring actual negative faces of a
counterexample pair. -/
theorem counterexample_ordered_adjacent_ratio_eq
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length) :
    ggvNegativeFacePairRatio P Q (ggvOrderedNegativeFaceSlopes P)[j] =
      ggvNegativeFacePairRatio P Q (ggvOrderedNegativeFaceSlopes P)[j+1] := by
  let t₁ := (ggvOrderedNegativeFaceSlopes P)[j]
  let t₂ := (ggvOrderedNegativeFaceSlopes P)[j+1]
  have hj₁ : j < (ggvOrderedNegativeFaceSlopes P).length := by omega
  have ht₁ : t₁ ∈ ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj₁
  have ht₂ : t₂ ∈ ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj
  obtain ⟨hdir₁, _, _, _⟩ :=
    ggv_ordered_negative_entry_canonical_face P t₁ ht₁
  obtain ⟨hdir₂, _, _, _⟩ :=
    ggv_ordered_negative_entry_canonical_face P t₂ ht₂
  have hp₁ := counterexample_vDeg_pos_all_directions
    P Q hpair (t₁.den : ℤ) t₁.num hdir₁
  have hp₂ := counterexample_vDeg_pos_all_directions
    P Q hpair (t₂.den : ℤ) t₂.num hdir₂
  obtain ⟨n, d, hn, hd, _, hw₁, hw₂⟩ :=
    counterexample_ordered_adjacent_common_weight_ratio P Q hpair j hj
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hp₁Q : (vDeg (t₁.den : ℤ) t₁.num P.1 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp₁)
  have hp₂Q : (vDeg (t₂.den : ℤ) t₂.num P.1 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp₂)
  have hw₁Q : (vDeg (t₁.den : ℤ) t₁.num P.1 : ℚ) * n =
      (vDeg (t₁.den : ℤ) t₁.num Q.1 : ℚ) * d := by
    exact_mod_cast hw₁
  have hw₂Q : (vDeg (t₂.den : ℤ) t₂.num P.1 : ℚ) * n =
      (vDeg (t₂.den : ℤ) t₂.num Q.1 : ℚ) * d := by
    exact_mod_cast hw₂
  have hratio₁ : ggvNegativeFacePairRatio P Q t₁ = (n : ℚ) / d := by
    apply (div_eq_div_iff hp₁Q hdQ).mpr
    exact hw₁Q.symm.trans (mul_comm _ _)
  have hratio₂ : ggvNegativeFacePairRatio P Q t₂ = (n : ℚ) / d := by
    apply (div_eq_div_iff hp₂Q hdQ).mpr
    exact hw₂Q.symm.trans (mul_comm _ _)
  exact hratio₁.trans hratio₂.symm

/-- Every entry of the actual finite negative-face list has the same
mate-to-source weighted-degree ratio as its first entry. -/
theorem counterexample_ordered_ratio_eq_first
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (i : ℕ) (hi : i < (ggvOrderedNegativeFaceSlopes P).length) :
    ggvNegativeFacePairRatio P Q (ggvOrderedNegativeFaceSlopes P)[i] =
      ggvNegativeFacePairRatio P Q (ggvOrderedNegativeFaceSlopes P)[0] := by
  induction i with
  | zero => rfl
  | succ k ih =>
      have hk : k < (ggvOrderedNegativeFaceSlopes P).length := by omega
      exact (counterexample_ordered_adjacent_ratio_eq P Q hpair k hi).symm.trans
        (ih hk)

end Dixmier.Weyl
