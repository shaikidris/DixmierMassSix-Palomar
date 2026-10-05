/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialHorizontalCutRectangle
public import DixmierFormal.Weyl.GGVMinimalPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Degree minimality under a horizontal polynomial cut

Preservation of both occupied rectangles preserves the degree gcd.
-/
namespace Dixmier.Weyl

/-- A common horizontal cut preserves degree-gcd minimality when both
source members have occupied subrectangular corners. -/
theorem degreeMinimal_horizontal_cut_preserved
    (P Q R S : A1 ℂ) (c : ℂ) (a b u v : ℕ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v)
    (hRS : IsCounterexamplePair R S)
    (hR : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P))
    (hS : polynomialRamifiedLift 1 S =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 Q)) :
    IsDegreeMinimalCounterexamplePair R S := by
  refine ⟨hRS, ?_⟩
  intro T U hTU
  rw [polynomial_horizontal_cut_preserves_totalDeg P R c a b hP hR,
    polynomial_horizontal_cut_preserves_totalDeg Q S c u v hQ hS]
  exact hmin.2 T U hTU

/-- Every common horizontal cut recovers a polynomial degree-minimal
pair with the same two occupied rectangles. -/
theorem degreeMinimal_horizontal_cut_recovers_pair
    (P Q : A1 ℂ) (c : ℂ) (a b u v : ℕ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧
      polynomialRamifiedLift 1 R =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) ∧
      polynomialRamifiedLift 1 S =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 Q) := by
  obtain ⟨R, S, hRS, hR, hS⟩ :=
    horizontal_cut_recovers_polynomial_counterexample c P Q hmin.1
  exact ⟨R, S,
    degreeMinimal_horizontal_cut_preserved P Q R S c a b u v hmin hP hQ hRS hR hS,
    polynomial_horizontal_cut_preserves_subrectangular P R c a b hP hR,
    polynomial_horizontal_cut_preserves_subrectangular Q S c u v hQ hS, hR, hS⟩

/-- The selected maximum-root cut produces a degree-minimal polynomial
pair with preserved rectangles and a negative-grade horizontal face. -/
theorem preliminary_degreeMinimal_horizontal_standardization
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (a b u v : ℕ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v)
    (hab : a < b) (hface : InDir 1 0 P.1) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧
      (∀ e ∈ (leadingForm 1 0 R.1).support, grade e < 0) := by
  obtain ⟨c, _, _, _, hext, _⟩ :=
    preliminary_horizontal_cut_negative_old_face_exact_pair
      hsource P Q hmin.1 a b hP hab hface
  obtain ⟨R, S, hminRS, hrectR, hrectS, hR, hS⟩ :=
    degreeMinimal_horizontal_cut_recovers_pair P Q c a b u v hmin hP hQ
  refine ⟨R, S, hminRS, hrectR, hrectS, ?_⟩
  intro e he
  have heR := (leadingForm_mem_iff_rational_slope R 1 0 (by norm_num) e).mp he
  have hle := heR.2 (expo a b) hrectR.1
  have ha : a ≤ e 0 := by
    dsimp [rationalNewtonWeight] at hle
    simp [expo] at hle
    exact_mod_cast hle
  have hea : e 0 = a := Nat.le_antisymm (hrectR.2 e heR.1).1 ha
  have hexpo : expo (e 0) (e 1) = e := by
    ext i
    fin_cases i <;> simp [expo]
  have hs : ((e 0 : ℤ), e 1) ∈ ramifiedPBWSupport 1 (by norm_num)
      (polynomialRamifiedLift 1 R) :=
    (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) R _ _).mpr
      ⟨e 0, by simp, hexpo.symm ▸ heR.1⟩
  rw [hR] at hs
  have hw : ramifiedWeight 1 1 0 ((e 0 : ℤ), e 1) = (a : ℤ) := by
    simp [ramifiedWeight, hea]
  simpa [grade] using (hext _ _ hs hw).2

/-- A negative horizontal face selects the strict-crossing alternative
from the actual ordered negative faces. -/
theorem preliminary_caseAlternative_of_negative_horizontal
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hterminal : ∀ e ∈ (leadingForm 1 0 P.1).support, grade e < 0) :
    CaseAlternative P.1 := by
  obtain ⟨j, hj, ρ, s, u, v, hρ, hs, hdir, _, hface, _, hu, hv, _, _, hupos, hvneg⟩ :=
    counterexample_ordered_strict_crossing_of_terminal hsource P Q hpair hterminal
  refine Or.inl ⟨(ρ : ℤ), -(s : ℤ), ?_, ?_, ?_, hdir.1,
    hface, ⟨u, hu, hupos⟩, ⟨v, hv, hvneg⟩⟩
  · exact_mod_cast hρ
  · have hsum := hdir.2
    omega
  · have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
    omega

/-- An oriented subrectangular degree-minimal pair can be retained or
horizontally cut to another degree-minimal pair with the same rectangles
and a strict-crossing case alternative. This does not claim mass preservation. -/
theorem preliminary_degreeMinimal_subrectangular_crossing_alternative
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (a b u v : ℕ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v)
    (hab : a < b) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧ CaseAlternative R.1 := by
  classical
  by_cases hface : InDir 1 0 P.1
  · obtain ⟨R, S, hminRS, hrectR, hrectS, hterminal⟩ :=
      preliminary_degreeMinimal_horizontal_standardization hsource P Q a b u v
        hmin hP hQ hab hface
    exact ⟨R, S, hminRS, hrectR, hrectS,
      preliminary_caseAlternative_of_negative_horizontal hsource R S hminRS.1 hterminal⟩
  · obtain ⟨w, hw, hwmin, hwneg⟩ :=
      subrectangular_horizontal_start_negative_of_no_dir P a b hP hab hface
    exact ⟨P, Q, hmin, hP, hQ,
      preliminary_caseAlternative_of_negative_horizontal hsource P Q hmin.1
        (horizontal_min_y_negative_all P w hw hwmin hwneg)⟩

end Dixmier.Weyl
