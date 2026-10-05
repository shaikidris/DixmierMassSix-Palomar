/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedGlobalRatio
public import DixmierFormal.Weyl.GGVActualFaceAdjacent

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The last negative face meets the horizontal boundary

The first tilt after the final strict-negative face cannot create
another negative face. It therefore reaches the horizontal face, whose
support need not itself have more than one point.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Every element of a sorted list is at most its last entry. -/
theorem sortedLT_mem_le_last
    (l : List ℚ) (hsorted : l.SortedLT)
    (j : ℕ) (hj : j + 1 = l.length)
    (u : ℚ) (hu : u ∈ l) : u ≤ l[j] := by
  let k := l.idxOf u
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr hu
  have hku : l[k] = u := List.getElem_idxOf hk
  have hjvalid : j < l.length := by omega
  have hkj : k ≤ j := by omega
  have hle : l[k] ≤ l[j] :=
    hsorted.getElem_le_getElem_iff.mpr hkj
  simpa only [hku] using hle

/-- The maximum-order occupied point of the last actual strict-negative
face also belongs to the horizontal leading face. No horizontal `InDir`
premise or degree bound is required. -/
theorem counterexample_last_negative_face_meets_horizontal
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (_hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j + 1 = (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] =
      (-(s : ℤ) : ℚ) / ρ)
    (hface : InDir (ρ : ℤ) (-(s : ℤ)) P.1) :
    ∃ a : Fin 2 →₀ ℕ,
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      a ∈ (leadingForm 1 0 P.1).support ∧
      (∀ p ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        p 1 ≤ a 1) := by
  classical
  obtain ⟨p, q, hp, _, _⟩ := Finset.one_lt_card_iff.mp hface
  obtain ⟨a, ha, haMax⟩ := Finset.exists_max_image
    (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support
      (fun e => e 1) ⟨p, hp⟩
  have hhorizontal : IsDirection 1 0 := by norm_num [IsDirection]
  have hHpos := counterexample_vDeg_pos_all_directions
    P Q hpair 1 0 hhorizontal
  have hHne := leadingForm_ne_zero_of_vDeg_pos P 1 0 hHpos
  obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr hHne
  have hltQ : (-(s : ℤ) : ℚ) / ρ < 0 := by
    have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
    have hρQ : (0 : ℚ) < ρ := by exact_mod_cast hρ
    exact div_neg_of_neg_of_pos (by norm_num at hsQ ⊢; exact hsQ) hρQ
  have hltR : ((-(s : ℤ) : ℝ) / ρ) < (0 : ℝ) := by
    exact_mod_cast hltQ
  obtain ⟨hyle, hyeq⟩ := leadingFace_points_ordered_by_slope
    P (ρ : ℤ) (-(s : ℤ)) 1 0 (by exact_mod_cast hρ)
      (by norm_num) (by simpa using hltR) ha hb
  rcases lt_or_eq_of_le hyle with hstrict | hequal
  · let t₁ : ℚ := (-(s : ℤ) : ℚ) / ρ
    let t₂ : ℚ := 0
    have haSupport :=
      (leadingForm_mem_iff_rational_slope
        P (ρ : ℤ) (-(s : ℤ)) (by exact_mod_cast hρ) a).mp ha |>.1
    have hbData :=
      (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) b).mp hb
    obtain ⟨t, ht₁, hmax, c, hcSupport, hcHigher, hcTie⟩ :=
      leadingFace_exists_first_upward_tilt
        P (ρ : ℤ) (-(s : ℤ)) (by exact_mod_cast hρ)
          a ha haMax ⟨b, hbData.1, hstrict⟩
    have hlater : rationalNewtonWeight t₂ a ≤
        rationalNewtonWeight t₂ b := by
      simpa [t₂] using hbData.2 a haSupport
    have ht₂ : t ≤ t₂ := by
      by_contra hbad
      have hgt : t₂ < t := lt_of_not_ge hbad
      have hy : (a 1 : ℚ) < b 1 := by exact_mod_cast hstrict
      have hprod : 0 < (t - t₂) * ((b 1 : ℚ) - a 1) :=
        mul_pos (sub_pos.mpr hgt) (sub_pos.mpr hy)
      have hfirst := hmax b hbData.1
      dsimp [rationalNewtonWeight] at hfirst hlater
      nlinarith [hfirst, hlater, hprod]
    have hleft : -1 < t₁ := by
      have hjvalid : j < (ggvOrderedNegativeFaceSlopes P).length := by omega
      have hmem : (ggvOrderedNegativeFaceSlopes P)[j] ∈
          ggvOrderedNegativeFaceSlopes P := List.getElem_mem hjvalid
      simpa only [hentry, t₁] using
        (ggv_ordered_negative_slope_bounds P _ hmem).1
    have htLeft : -1 < t := lt_trans hleft ht₁
    have htZero : t = 0 := by
      by_contra hne
      have htNeg : t < 0 := by
        have hle : t ≤ 0 := by simpa [t₂] using ht₂
        exact lt_of_le_of_ne hle hne
      have hac : a ≠ c := by
        intro heq
        rw [← heq] at hcHigher
        exact (Nat.lt_irrefl _) hcHigher
      obtain ⟨_, _, htList⟩ :=
        rationalSlope_two_maximizers_mem_ordered_negative_slopes
          P t htLeft htNeg a c haSupport hcSupport hmax hcTie hac
      have hle := sortedLT_mem_le_last
        (ggvOrderedNegativeFaceSlopes P)
        (ggv_ordered_negative_slopes_strict P) j hj t htList
      rw [hentry] at hle
      exact (not_le_of_gt ht₁) hle
    have haHoriz := rationalSlope_maximizer_mem_leadingForm P t a haSupport hmax
    have htDen : (0 : ℤ) < t.den := by exact_mod_cast Rat.den_pos t
    have haRat :=
      (leadingForm_mem_iff_rational_slope P (t.den : ℤ) t.num htDen a).mp haHoriz
    have hnorm : (t.num : ℚ) / ((t.den : ℤ) : ℚ) = t := by
      simpa using Rat.num_div_den t
    rw [hnorm, htZero] at haRat
    have haH : a ∈ (leadingForm 1 0 P.1).support :=
      (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) a).mpr
        (by simpa using haRat)
    exact ⟨a, ha, haH, haMax⟩
  · have hab : a = b := hyeq hequal
    exact ⟨a, ha, hab ▸ hb, haMax⟩

end Dixmier.Weyl
