/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalLastZeroExclusion
public import DixmierFormal.Weyl.GGVDiagonalMonomialCases

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Complete singleton diagonal case map

Both axis cases and the interior case satisfy the original-or-Fourier
alternative, with preliminary companion and degree inputs explicit.
-/
namespace Dixmier.Weyl

/-- Every singleton diagonal face belongs to the original-or-Fourier case map. -/
theorem preliminary_singleton_diagonal_complete_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hdiag : totalDeg P.1 = a+b)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo a b) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  by_cases ha : a = 0
  · subst a
    exact Or.inl (preliminary_y_axis_diagonal_caseAlternative_of_companion hsource hdegree
      P Q hpair b (by simpa using hdiag) hunique)
  · by_cases hb : b = 0
    · subst b
      have hpos : 0 < a+0 := by omega
      obtain ⟨hFmem,hFunique⟩ := fourier_diagonal_face_unique P a 0 hdiag hpos hunique
      have hFdegree : totalDeg (fourierAlgHom ℂ P).1 = a := by
        rw [totalDeg_fourier_eq,hdiag]; simp
      have hc := preliminary_y_axis_diagonal_caseAlternative_of_companion hsource hdegree
        (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) (isCounterexamplePair_fourier P Q hpair)
        a hFdegree hFunique
      exact Or.inr (by simpa only [fourier_eq_algHom] using hc)
    · exact preliminary_positive_singleton_diagonal_caseSplit hsource P Q hpair a b
        hdiag hmem hunique (by omega) (by omega)

/-- All diagonal monomials, including the axis powers, satisfy the case map. -/
theorem preliminary_diagonal_monomial_complete_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (lam : ℂ) (a b : ℕ) (hlam : lam ≠ 0)
    (hface : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      MvPolynomial.X 0^a * MvPolynomial.X 1^b) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  have hs : (leadingForm 1 1 P.1).support = {expo a b} := by
    rw [hface]; exact weighted_monomial_support lam hlam a b
  have hm : expo a b ∈ (leadingForm 1 1 P.1).support := by rw [hs]; simp
  have hw := (polynomialFace_point_source_data P 1 1 a b hm).2
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
    (by norm_num [IsDirection])
  have ht := totalDeg_eq_vDeg_one_one P hp
  have hd : totalDeg P.1 = a+b := by norm_num at hw; omega
  exact preliminary_singleton_diagonal_complete_caseSplit hsource hdegree P Q hpair a b hd
    hm (by intro d hd; simpa [hs] using hd)

end Dixmier.Weyl
