/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVRationalDirection
public import DixmierFormal.Weyl.GGVFiniteFaceSlopes

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical integer normals for ordered actual faces

Every slope in the finite ordered list comes from a genuine primitive
negative face. The reduced denominator and numerator of the rational
slope are that face's unique primitive integer normal.
-/

namespace Dixmier.Weyl

/-- The rational numerator and denominator of each ordered list entry
give the actual primitive negative face of the operator. -/
theorem ggv_ordered_negative_entry_canonical_face
    (P : A1 ℂ) (t : ℚ)
    (ht : t ∈ ggvOrderedNegativeFaceSlopes P) :
    IsDirection (t.den : ℤ) t.num ∧
      0 < (t.den : ℤ) ∧ t.num < 0 ∧
      InDir (t.den : ℤ) t.num P.1 := by
  obtain ⟨hleft, hright⟩ := ggv_ordered_negative_slope_bounds P t ht
  obtain ⟨hcanon, hden, hnum, hslope⟩ :=
    rationalSlope_primitive_negative_direction t hleft hright
  obtain ⟨⟨ρ, σ⟩, ⟨hdir, hρ, _, hface⟩, heq⟩ :=
    (mem_ggvOrderedNegativeFaceSlopes_iff P t).mp ht
  have hnorm : (σ : ℚ) / (ρ : ℚ) = (t.num : ℚ) / (t.den : ℚ) := by
    exact heq.symm.trans hslope.symm
  obtain ⟨hρeq, hσeq⟩ :=
    ggv_primitive_negative_normal_unique
      ρ σ (t.den : ℤ) t.num hdir hcanon hρ hden hnorm
  exact ⟨hcanon, hden, hnum, by simpa [hρeq, hσeq] using hface⟩

/-- The same canonical entry in the natural `(ρ,-s)` notation used by
the strict-negative face and cut theorems. -/
theorem ggv_ordered_negative_entry_nat_face
    (P : A1 ℂ) (t : ℚ)
    (ht : t ∈ ggvOrderedNegativeFaceSlopes P) :
    ∃ ρ s : ℕ, 0 < ρ ∧ 0 < s ∧
      IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      InDir (ρ : ℤ) (-(s : ℤ)) P.1 ∧
      t = (-(s : ℤ) : ℚ) / ρ ∧
      (ρ : ℤ) = (t.den : ℤ) ∧ -(s : ℤ) = t.num := by
  obtain ⟨hdir, hden, hnum, hface⟩ :=
    ggv_ordered_negative_entry_canonical_face P t ht
  let ρ : ℕ := t.den
  let s : ℕ := (-t.num).toNat
  have hρ : 0 < ρ := by exact_mod_cast hden
  have hs : 0 < s := by
    dsimp [s]
    omega
  have hsCast : -(s : ℤ) = t.num := by
    dsimp [s]
    omega
  refine ⟨ρ, s, hρ, hs, ?_, ?_, ?_, rfl, hsCast⟩
  · simpa [ρ, hsCast] using hdir
  · simpa [ρ, hsCast] using hface
  · have hsCastQ : -((s : ℤ) : ℚ) = (t.num : ℚ) := by
      exact_mod_cast hsCast
    simpa only [ρ, hsCastQ] using (Rat.num_div_den t).symm

end Dixmier.Weyl
