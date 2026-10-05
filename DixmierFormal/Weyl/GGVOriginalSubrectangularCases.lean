/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVHorizontalMinimality

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Original-pair alternatives for subrectangular counterexamples

The occupied negative-grade corner supplies the negative horizontal point.
The preliminary companion excludes a zero-grade horizontal maximum. The
case alternative is obtained for the original member or its Fourier image;
no shear or mass preservation under a cut is used.
-/
namespace Dixmier.Weyl

/-- A nonpositive horizontal face is strictly negative under the
preliminary companion input. -/
theorem preliminary_horizontal_nonpositive_is_negative
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hnonpos : ∀ e ∈ (leadingForm 1 0 P.1).support, grade e ≤ 0) :
    ∀ e ∈ (leadingForm 1 0 P.1).support, grade e < 0 := by
  intro e he
  have hle := hnonpos e he
  by_contra hbad
  have hzero : grade e = 0 := by omega
  have hdiag : e 0 = e 1 := by dsimp [grade] at hzero; omega
  have hexpo : expo (e 0) (e 1) = e := by
    ext i
    fin_cases i <;> simp [expo]
  have hw := (polynomialFace_point_source_data P 1 0 (e 0) (e 1)
    (hexpo.symm ▸ he)).2
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 0
    (by norm_num [IsDirection])
  have hpos : 0 < e 0 := by
    have hx : (e 0 : ℤ) = vDeg 1 0 P.1 := by simpa using hw
    rw [← hx] at hp
    exact_mod_cast hp
  have hmax : ∀ x ∈ (leadingForm 1 0 P.1).support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) e := by
    intro x hx
    have hg : grade x ≤ grade e := by rw [hzero]; exact hnonpos x hx
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, grade,
      mul_comm, sub_eq_add_neg] using hg
  exact ggv_preliminary_no_diagonal_leading_top hsource P Q hpair
    1 0 (by norm_num [IsDirection]) he hmax hdiag hpos

/-- A negative-grade point on the horizontal face suffices for the
original member's case alternative; no rectangle hypothesis is needed. -/
theorem preliminary_horizontal_negative_point_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hnegative : ∃ e ∈ (leadingForm 1 0 P.1).support, grade e < 0) :
    CaseAlternative P.1 := by
  classical
  obtain ⟨e, he, heNeg⟩ := hnegative
  by_cases hpos : ∃ f ∈ (leadingForm 1 0 P.1).support, 0 < grade f
  · obtain ⟨f, hf, hfPos⟩ := hpos
    have hne : f ≠ e := by intro h; rw [h] at hfPos; omega
    have hface : InDir 1 0 P.1 :=
      Finset.one_lt_card_iff.mpr ⟨f, e, hf, he, hne⟩
    exact Or.inl ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num,
      hface, ⟨f, hf, hfPos⟩, ⟨e, he, heNeg⟩⟩
  · have hnonpos : ∀ f ∈ (leadingForm 1 0 P.1).support, grade f ≤ 0 := by
      intro f hf
      by_contra h
      exact hpos ⟨f, hf, by omega⟩
    exact preliminary_caseAlternative_of_negative_horizontal hsource P Q hpair
      (preliminary_horizontal_nonpositive_is_negative hsource P Q hpair hnonpos)

/-- The oriented rectangle gives the strict-crossing alternative for
the original member, including a possible horizontal crossing. -/
theorem preliminary_subrectangular_original_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b) (hab : a < b) :
    CaseAlternative P.1 := by
  apply preliminary_horizontal_negative_point_caseAlternative hsource P Q hpair
  exact ⟨expo a b, subrectangular_corner_mem_horizontal P a b hrect,
    by simp [grade, expo]; omega⟩

/-- Any positive-degree subrectangular counterexample satisfies the
frozen original-or-Fourier case alternative under the preliminary companion. -/
theorem preliminary_subrectangular_original_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b) (hpos : 0 < a + b) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  have hne := counterexample_subrectangular_corner_not_diagonal
    hsource P Q hpair a b hrect hpos
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact Or.inl (preliminary_subrectangular_original_caseAlternative
      hsource P Q hpair a b hrect hab)
  · have hFrect := subrectangular_fourier_at P a b hrect hpos
    have hFpair := isCounterexamplePair_fourier P Q hpair
    have hcase := preliminary_subrectangular_original_caseAlternative
      hsource (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) hFpair b a hFrect hba
    exact Or.inr (by simpa only [fourier_eq_algHom] using hcase)

/-- The positive singleton-diagonal branch of the published case map
satisfies the original-or-Fourier alternative without assuming a rectangle. -/
theorem preliminary_positive_singleton_diagonal_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hdegree : totalDeg P.1 = a + b)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b)
    (ha : 0 < a) (hb : 0 < b) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  have hrect := preliminary_companion_singleton_diagonal_subrectangular
    hsource P Q hpair a b hdegree hmem hunique ha hb
  exact preliminary_subrectangular_original_caseSplit hsource P Q hpair a b hrect (by omega)

end Dixmier.Weyl
