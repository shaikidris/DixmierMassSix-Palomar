/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVActualFaceAdjacent

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Successive actual Newton-face slopes

The finite ordered carrier has no member strictly between two
successive entries. Combined with the first-tilt construction, this
identifies the common endpoint of two successive actual faces.
-/

namespace Dixmier.Weyl

/-- In a strictly sorted list, any listed element above entry `j` is
at least the successor entry `j+1`. -/
theorem sortedLT_next_le_of_mem_gt
    (l : List ℚ) (hsorted : l.SortedLT)
    (j : ℕ) (hj : j + 1 < l.length)
    (u : ℚ) (hu : u ∈ l)
    (hgt : l[j] < u) :
    l[j+1] ≤ u := by
  have hj0 : j < l.length := by omega
  let k := l.idxOf u
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr hu
  have hku : l[k] = u := List.getElem_idxOf hk
  have hjk : j < k := by
    by_contra hbad
    have hkj : k ≤ j := Nat.le_of_not_gt hbad
    have hle : l[k] ≤ l[j] :=
      hsorted.getElem_le_getElem_iff.mpr hkj
    rw [hku] at hle
    exact (not_le_of_gt hgt) hle
  have hj1k : j + 1 ≤ k := by omega
  have hle : l[j+1] ≤ l[k] :=
    hsorted.getElem_le_getElem_iff.mpr hj1k
  simpa only [hku] using hle

/-- The last point of an actual face belongs to the next face in the
ordered negative-direction list, provided the later face has a point
of strictly higher derivative order. -/
theorem leadingFace_last_point_mem_successor_list_face
    (P : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hleft : -1 < (σ₁ : ℚ) / ρ₁)
    (hright : (σ₂ : ℚ) / ρ₂ < 0)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length)
    (hfirst : (ggvOrderedNegativeFaceSlopes P)[j] = (σ₁ : ℚ) / ρ₁)
    (hsecond : (ggvOrderedNegativeFaceSlopes P)[j+1] = (σ₂ : ℚ) / ρ₂)
    (a b : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm ρ₁ σ₁ P.1).support)
    (hb : b ∈ (leadingForm ρ₂ σ₂ P.1).support)
    (hlast : ∀ p ∈ (leadingForm ρ₁ σ₁ P.1).support,
      p 1 ≤ a 1) :
    a ∈ (leadingForm ρ₂ σ₂ P.1).support := by
  have hltList : (ggvOrderedNegativeFaceSlopes P)[j] <
      (ggvOrderedNegativeFaceSlopes P)[j+1] :=
    (ggv_ordered_negative_slopes_strict P).getElem_lt_getElem_of_lt
      (Nat.lt_succ_self j)
  have hltQ : (σ₁ : ℚ) / ρ₁ < (σ₂ : ℚ) / ρ₂ := by
    calc
      (σ₁ : ℚ) / ρ₁ = (ggvOrderedNegativeFaceSlopes P)[j] := hfirst.symm
      _ < (ggvOrderedNegativeFaceSlopes P)[j+1] := hltList
      _ = (σ₂ : ℚ) / ρ₂ := hsecond
  have hltR : (σ₁ : ℝ) / ρ₁ < (σ₂ : ℝ) / ρ₂ := by
    exact_mod_cast hltQ
  obtain ⟨hle,heq⟩ :=
    leadingFace_points_ordered_by_slope
      P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hltR ha hb
  rcases lt_or_eq_of_le hle with hstrict | hequal
  · apply leadingFace_last_point_mem_next_face
      P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hleft hright a b ha hb hlast hstrict
    intro u hu hgt
    have hgt' : (ggvOrderedNegativeFaceSlopes P)[j] < u := by
      rw [hfirst]
      exact hgt
    have hle' := sortedLT_next_le_of_mem_gt
      (ggvOrderedNegativeFaceSlopes P)
      (ggv_ordered_negative_slopes_strict P) j hj u hu hgt'
    rwa [hsecond] at hle'
  · have hab : a = b := heq hequal
    simpa only [hab] using hb

/-- Successive genuine negative faces have an occupied shared vertex:
it is the maximum-order point of the earlier face and the
minimum-order point of the later face. -/
theorem leadingFace_successor_shared_endpoint
    (P : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hleft : -1 < (σ₁ : ℚ) / ρ₁)
    (hright : (σ₂ : ℚ) / ρ₂ < 0)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length)
    (hfirst : (ggvOrderedNegativeFaceSlopes P)[j] = (σ₁ : ℚ) / ρ₁)
    (hsecond : (ggvOrderedNegativeFaceSlopes P)[j+1] = (σ₂ : ℚ) / ρ₂)
    (hface₁ : InDir ρ₁ σ₁ P.1)
    (hface₂ : InDir ρ₂ σ₂ P.1) :
    ∃ a : Fin 2 →₀ ℕ,
      a ∈ (leadingForm ρ₁ σ₁ P.1).support ∧
      a ∈ (leadingForm ρ₂ σ₂ P.1).support ∧
      (∀ p ∈ (leadingForm ρ₁ σ₁ P.1).support, p 1 ≤ a 1) ∧
      (∀ q ∈ (leadingForm ρ₂ σ₂ P.1).support, a 1 ≤ q 1) := by
  obtain ⟨p,q,hp,hq,_⟩ := Finset.one_lt_card_iff.mp hface₁
  have hne₁ : (leadingForm ρ₁ σ₁ P.1).support.Nonempty := ⟨p,hp⟩
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image
    (leadingForm ρ₁ σ₁ P.1).support (fun d => d 1) hne₁
  obtain ⟨b,c,hb,hc,_⟩ := Finset.one_lt_card_iff.mp hface₂
  have ha₂ := leadingFace_last_point_mem_successor_list_face
    P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hleft hright j hj hfirst hsecond
      a b ha hb hmax
  have hltList : (ggvOrderedNegativeFaceSlopes P)[j] <
      (ggvOrderedNegativeFaceSlopes P)[j+1] :=
    (ggv_ordered_negative_slopes_strict P).getElem_lt_getElem_of_lt
      (Nat.lt_succ_self j)
  have hltQ : (σ₁ : ℚ) / ρ₁ < (σ₂ : ℚ) / ρ₂ := by
    calc
      (σ₁ : ℚ) / ρ₁ = (ggvOrderedNegativeFaceSlopes P)[j] := hfirst.symm
      _ < (ggvOrderedNegativeFaceSlopes P)[j+1] := hltList
      _ = (σ₂ : ℚ) / ρ₂ := hsecond
  have hltR : (σ₁ : ℝ) / ρ₁ < (σ₂ : ℝ) / ρ₂ := by
    exact_mod_cast hltQ
  refine ⟨a,ha,ha₂,hmax,?_⟩
  intro d hd
  exact (leadingFace_points_ordered_by_slope
    P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hltR ha hd).1

end Dixmier.Weyl
