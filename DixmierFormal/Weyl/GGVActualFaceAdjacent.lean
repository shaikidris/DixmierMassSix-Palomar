/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVRationalDirection

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# An actual negative face between two ordered faces

The first rational tilt from an earlier face is bounded above by a
later face with a higher derivative-order point. Hence the tilt lies
in the admissible negative interval and is an actual primitive face.
This does not yet identify it as the immediate successor in the list.
-/

namespace Dixmier.Weyl

/-- Between an earlier negative face's last point and a later face's
higher-order point, the finite first tilt gives an actual negative
face no later than the given later slope. -/
theorem leadingFace_exists_intermediate_actual_negative_face
    (P : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hleft : -1 < (σ₁ : ℚ) / ρ₁)
    (hright : (σ₂ : ℚ) / ρ₂ < 0)
    (a b : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm ρ₁ σ₁ P.1).support)
    (hb : b ∈ (leadingForm ρ₂ σ₂ P.1).support)
    (hlast : ∀ p ∈ (leadingForm ρ₁ σ₁ P.1).support,
      p 1 ≤ a 1)
    (hhigher : a 1 < b 1) :
    ∃ t : ℚ, (σ₁ : ℚ) / ρ₁ < t ∧
      t ≤ (σ₂ : ℚ) / ρ₂ ∧
      t ∈ ggvOrderedNegativeFaceSlopes P ∧
      a ∈ (leadingForm (t.den : ℤ) t.num P.1).support ∧
      ∃ c ∈ (leadingForm (t.den : ℤ) t.num P.1).support,
        a 1 < c 1 := by
  let t₁ : ℚ := (σ₁ : ℚ) / ρ₁
  let t₂ : ℚ := (σ₂ : ℚ) / ρ₂
  have haSupport := (leadingForm_mem_iff_rational_slope P ρ₁ σ₁ hρ₁ a).mp ha |>.1
  have hbData := (leadingForm_mem_iff_rational_slope P ρ₂ σ₂ hρ₂ b).mp hb
  obtain ⟨t,ht₁,hmax,c,hcSupport,hcHigher,hcTie⟩ :=
    leadingFace_exists_first_upward_tilt P ρ₁ σ₁ hρ₁ a ha hlast
      ⟨b,hbData.1,hhigher⟩
  have hlater : rationalNewtonWeight t₂ a ≤ rationalNewtonWeight t₂ b :=
    hbData.2 a haSupport
  have ht₂ : t ≤ t₂ := by
    by_contra hbad
    have hgt : t₂ < t := lt_of_not_ge hbad
    have hy : (a 1 : ℚ) < b 1 := by exact_mod_cast hhigher
    have hprod : 0 < (t - t₂) * ((b 1 : ℚ) - a 1) :=
      mul_pos (sub_pos.mpr hgt) (sub_pos.mpr hy)
    have hfirst := hmax b hbData.1
    dsimp [rationalNewtonWeight] at hfirst hlater
    nlinarith [hfirst,hlater,hprod]
  have htLeft : -1 < t := lt_trans hleft ht₁
  have htRight : t < 0 := lt_of_le_of_lt ht₂ hright
  have hne : a ≠ c := by
    intro heq
    rw [← heq] at hcHigher
    exact (Nat.lt_irrefl _) hcHigher
  obtain ⟨_,_,htList⟩ :=
    rationalSlope_two_maximizers_mem_ordered_negative_slopes
      P t htLeft htRight a c haSupport hcSupport hmax hcTie hne
  have haFace := rationalSlope_maximizer_mem_leadingForm P t a haSupport hmax
  have hcMax : ∀ p ∈ (symbol P.1).support,
      rationalNewtonWeight t p ≤ rationalNewtonWeight t c := by
    intro p hp
    exact (hmax p hp).trans_eq hcTie.symm
  have hcFace := rationalSlope_maximizer_mem_leadingForm P t c hcSupport hcMax
  exact ⟨t,ht₁,ht₂,htList,haFace,c,hcFace,hcHigher⟩

/-- If the later slope is the next actual negative-face slope after
the earlier one, the last point of the earlier face belongs to the
later face. The `hnext` premise is the exact no-intervening-entry
property; extracting it from adjacent indices of the sorted list is
left to the list-level adapter. -/
theorem leadingFace_last_point_mem_next_face
    (P : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hleft : -1 < (σ₁ : ℚ) / ρ₁)
    (hright : (σ₂ : ℚ) / ρ₂ < 0)
    (a b : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm ρ₁ σ₁ P.1).support)
    (hb : b ∈ (leadingForm ρ₂ σ₂ P.1).support)
    (hlast : ∀ p ∈ (leadingForm ρ₁ σ₁ P.1).support,
      p 1 ≤ a 1)
    (hhigher : a 1 < b 1)
    (hnext : ∀ u ∈ ggvOrderedNegativeFaceSlopes P,
      (σ₁ : ℚ) / ρ₁ < u → (σ₂ : ℚ) / ρ₂ ≤ u) :
    a ∈ (leadingForm ρ₂ σ₂ P.1).support := by
  obtain ⟨t,ht₁,ht₂,htList,haFace,_⟩ :=
    leadingFace_exists_intermediate_actual_negative_face
      P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hleft hright a b ha hb hlast hhigher
  have heq : t = (σ₂ : ℚ) / ρ₂ :=
    le_antisymm ht₂ (hnext t htList ht₁)
  have htDen : (0 : ℤ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have haRat :=
    (leadingForm_mem_iff_rational_slope P (t.den : ℤ) t.num htDen a).mp haFace
  have hnorm : (t.num : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    simpa using Rat.num_div_den t
  rw [hnorm, heq] at haRat
  exact (leadingForm_mem_iff_rational_slope P ρ₂ σ₂ hρ₂ a).mpr haRat

end Dixmier.Weyl
