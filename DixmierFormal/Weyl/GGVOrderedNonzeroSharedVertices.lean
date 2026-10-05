/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVNegativeFaceZeroGrade
public import DixmierFormal.Weyl.GGVOrderedFaceSuccessor

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Nonzero grades at adjacent actual negative faces

The endpoint shared by two successive faces is the first endpoint of
the later face. The preliminary G13 companion excludes zero grade at
that endpoint. This is conditional on companion existence, not a proof
of that source theorem.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Conditional on the G13 preliminary companion, every consecutive
pair of actual strict-negative faces shares a nonzero-grade endpoint. -/
theorem ggv_preliminary_successor_shared_grade_ne_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length) :
    let t₁ := (ggvOrderedNegativeFaceSlopes P)[j]
    let t₂ := (ggvOrderedNegativeFaceSlopes P)[j+1]
    ∃ a : Fin 2 →₀ ℕ,
      a ∈ (leadingForm (t₁.den : ℤ) t₁.num P.1).support ∧
      a ∈ (leadingForm (t₂.den : ℤ) t₂.num P.1).support ∧
      (∀ p ∈ (leadingForm (t₁.den : ℤ) t₁.num P.1).support,
        p 1 ≤ a 1) ∧
      (∀ p ∈ (leadingForm (t₂.den : ℤ) t₂.num P.1).support,
        a 1 ≤ p 1) ∧ grade a ≠ 0 := by
  let t₁ := (ggvOrderedNegativeFaceSlopes P)[j]
  let t₂ := (ggvOrderedNegativeFaceSlopes P)[j+1]
  have hj₁ : j < (ggvOrderedNegativeFaceSlopes P).length := by omega
  have ht₁ : t₁ ∈ ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj₁
  have ht₂ : t₂ ∈ ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj
  obtain ⟨ρ₁, s₁, hρ₁, hs₁, _, hface₁, hslope₁, hρeq₁, hσeq₁⟩ :=
    ggv_ordered_negative_entry_nat_face P t₁ ht₁
  obtain ⟨ρ₂, s₂, hρ₂, hs₂, hdir₂, hface₂, hslope₂, hρeq₂, hσeq₂⟩ :=
    ggv_ordered_negative_entry_nat_face P t₂ ht₂
  have hleft : -1 < (-(s₁ : ℤ) : ℚ) / ρ₁ := by
    rw [← hslope₁]
    exact (ggv_ordered_negative_slope_bounds P t₁ ht₁).1
  have hright : (-(s₂ : ℤ) : ℚ) / ρ₂ < 0 := by
    rw [← hslope₂]
    exact (ggv_ordered_negative_slope_bounds P t₂ ht₂).2
  obtain ⟨a, ha₁, ha₂, haMax, haMin⟩ :=
    leadingFace_successor_shared_endpoint
      P (ρ₁ : ℤ) (-(s₁ : ℤ)) (ρ₂ : ℤ) (-(s₂ : ℤ))
      (by exact_mod_cast hρ₁) (by exact_mod_cast hρ₂)
      hleft hright j hj hslope₁ hslope₂ hface₁ hface₂
  have hne := ggv_preliminary_negative_face_min_y_grade_ne_zero
    hsource P Q hpair ρ₂ s₂ hρ₂ hs₂ hdir₂ a ha₂ haMin
  refine ⟨a, ?_, ?_, ?_, ?_, hne⟩
  · simpa only [hρeq₁, hσeq₁] using ha₁
  · simpa only [hρeq₂, hσeq₂] using ha₂
  · simpa only [hρeq₁, hσeq₁] using haMax
  · simpa only [hρeq₂, hσeq₂] using haMin

end Dixmier.Weyl
