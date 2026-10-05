/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFaceFirstDownwardTilt
public import DixmierFormal.Weyl.GGVRationalDirection
public import DixmierFormal.Weyl.GGVOrderedFaceCanonical
public import DixmierFormal.Weyl.GGVPositiveWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The first negative face meets the diagonal boundary

The first downward tilt from the first strict-negative face cannot
create another negative face. It therefore reaches the diagonal face,
which may itself have a single occupied point.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Every member of a sorted nonempty list is at least its first entry. -/
theorem sortedLT_first_le_mem
    (l : List ℚ) (hsorted : l.SortedLT)
    (hzero : 0 < l.length) (u : ℚ) (hu : u ∈ l) : l[0] ≤ u := by
  let k := l.idxOf u
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr hu
  have hku : l[k] = u := List.getElem_idxOf hk
  have hle : l[0] ≤ l[k] :=
    hsorted.getElem_le_getElem_iff.mpr (Nat.zero_le k)
  simpa only [hku] using hle

private theorem rationalNewtonWeight_neg_one_eq_grade
    (e : Fin 2 →₀ ℕ) : rationalNewtonWeight (-1) e = grade e := by
  simp [rationalNewtonWeight, grade]
  ring

/-- The minimum-order occupied point of the first actual negative face
also belongs to the diagonal leading face. No diagonal `InDir` premise
or degree bound is required. -/
theorem first_negative_face_meets_diagonal
    (P : A1 ℂ) (ρ s : ℕ) (hρ : 0 < ρ) (_hs : 0 < s)
    (hzero : 0 < (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[0] =
      (-(s : ℤ) : ℚ) / ρ)
    (hface : InDir (ρ : ℤ) (-(s : ℤ)) P.1)
    (b : Fin 2 →₀ ℕ)
    (hb : b ∈ (leadingForm 1 (-1) P.1).support) :
    ∃ a : Fin 2 →₀ ℕ,
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      a ∈ (leadingForm 1 (-1) P.1).support ∧
      (∀ p ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        a 1 ≤ p 1) := by
  classical
  obtain ⟨p, q, hp, _, _⟩ := Finset.one_lt_card_iff.mp hface
  obtain ⟨a, ha, haMin⟩ := Finset.exists_min_image
    (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support
      (fun e => e 1) ⟨p, hp⟩
  have hfirstMem : (ggvOrderedNegativeFaceSlopes P)[0] ∈
      ggvOrderedNegativeFaceSlopes P := List.getElem_mem hzero
  have hltQ : -1 < (-(s : ℤ) : ℚ) / ρ := by
    simpa only [hentry] using
      (ggv_ordered_negative_slope_bounds P _ hfirstMem).1
  have hltR : (-1 : ℝ) < ((-(s : ℤ) : ℝ) / ρ) := by
    exact_mod_cast hltQ
  obtain ⟨hyle, hyeq⟩ := leadingFace_points_ordered_by_slope
    P 1 (-1) (ρ : ℤ) (-(s : ℤ)) (by norm_num)
      (by exact_mod_cast hρ) (by simpa using hltR) hb ha
  rcases lt_or_eq_of_le hyle with hstrict | hequal
  · let t₁ : ℚ := (-(s : ℤ) : ℚ) / ρ
    have haSupport :=
      (leadingForm_mem_iff_rational_slope
        P (ρ : ℤ) (-(s : ℤ)) (by exact_mod_cast hρ) a).mp ha |>.1
    have hbData :=
      (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) b).mp hb
    obtain ⟨t, ht₁, hmax, c, hcSupport, hcLower, hcTie⟩ :=
      leadingFace_exists_first_downward_tilt
        P (ρ : ℤ) (-(s : ℤ)) (by exact_mod_cast hρ)
          a ha haMin ⟨b, hbData.1, hstrict⟩
    have hdiag : rationalNewtonWeight (-1) a ≤
        rationalNewtonWeight (-1) b := by
      simpa using hbData.2 a haSupport
    have htLower : -1 ≤ t := by
      by_contra hbad
      have hlt : t < -1 := lt_of_not_ge hbad
      have hy : (b 1 : ℚ) < a 1 := by exact_mod_cast hstrict
      have hprod : 0 < ((-1 : ℚ) - t) * ((a 1 : ℚ) - b 1) :=
        mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hy)
      have hfirst := hmax b hbData.1
      dsimp [rationalNewtonWeight] at hfirst hdiag
      nlinarith [hfirst, hdiag, hprod]
    have htEq : t = -1 := by
      by_contra hne
      have htGt : -1 < t := lt_of_le_of_ne htLower (Ne.symm hne)
      have htNeg : t < 0 := by
        have ht₁neg : t₁ < 0 := by
          simpa only [hentry, t₁] using
            (ggv_ordered_negative_slope_bounds P _ hfirstMem).2
        exact lt_trans ht₁ ht₁neg
      have hac : a ≠ c := by
        intro heq
        rw [← heq] at hcLower
        exact (Nat.lt_irrefl _) hcLower
      obtain ⟨_, _, htList⟩ :=
        rationalSlope_two_maximizers_mem_ordered_negative_slopes
          P t htGt htNeg a c haSupport hcSupport hmax hcTie hac
      have hle := sortedLT_first_le_mem
        (ggvOrderedNegativeFaceSlopes P)
        (ggv_ordered_negative_slopes_strict P) hzero t htList
      rw [hentry] at hle
      exact (not_le_of_gt ht₁) hle
    have haH : a ∈ (leadingForm 1 (-1) P.1).support :=
      (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) a).mpr
        ⟨haSupport, by
          intro e he
          have h := hmax e he
          rw [htEq] at h
          simpa using h⟩
    exact ⟨a, ha, haH, haMin⟩
  · have hab : b = a := hyeq hequal
    exact ⟨a, ha, hab ▸ hb, haMin⟩

/-- The first actual strict-negative face of a counterexample member
starts at a positive-grade point on the diagonal face. -/
theorem counterexample_first_negative_diagonal_positive_start
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hzero : 0 < (ggvOrderedNegativeFaceSlopes P).length) :
    ∃ (ρ s : ℕ) (a : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes P)[0] = (-(s : ℤ) : ℚ) / ρ ∧
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      a ∈ (leadingForm 1 (-1) P.1).support ∧
      (∀ p ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        a 1 ≤ p 1) ∧ 0 < grade a := by
  have hmem : (ggvOrderedNegativeFaceSlopes P)[0] ∈
      ggvOrderedNegativeFaceSlopes P := List.getElem_mem hzero
  obtain ⟨ρ, s, hρ, hs, hdir, hface, hentry, _, _⟩ :=
    ggv_ordered_negative_entry_nat_face P _ hmem
  obtain ⟨d, hd, hdpos⟩ := (ggv_grades_opposite_proved P Q hpair).1
  obtain ⟨b, hbSymbol, hbMax⟩ :=
    Finset.exists_max_image (symbol P.1).support grade ⟨d, hd⟩
  have hbDiag : b ∈ (leadingForm 1 (-1) P.1).support :=
    (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) b).mpr
      ⟨hbSymbol, by
        intro e he
        simpa [rationalNewtonWeight_neg_one_eq_grade] using hbMax e he⟩
  obtain ⟨a, haFace, haDiag, haMin⟩ :=
    first_negative_face_meets_diagonal
      P ρ s hρ hs hzero hentry hface b hbDiag
  have haSymbol :=
    (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) a).mp haDiag
  have hbMaxRat :=
    (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) b).mp hbDiag
  have hgradeEq : grade a = grade b := by
    have hab := hbMaxRat.2 a haSymbol.1
    have hba := haSymbol.2 b hbSymbol
    have hab' : grade a ≤ grade b := by
      simpa [rationalNewtonWeight_neg_one_eq_grade] using hab
    have hba' : grade b ≤ grade a := by
      simpa [rationalNewtonWeight_neg_one_eq_grade] using hba
    exact le_antisymm hab' hba'
  have hbpos : 0 < grade b := lt_of_lt_of_le hdpos (hbMax d hd)
  exact ⟨ρ, s, a, hρ, hs, hdir, hentry, haFace, haDiag, haMin,
    hgradeEq ▸ hbpos⟩

end Dixmier.Weyl
