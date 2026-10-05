/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DiagonalYFactorDispatch
public import DixmierFormal.Weyl.PositiveBinomialTopBoundary

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Complete one-root dispatch with a residual X-axis factor

The diagonal top point transfers exactly through Fourier. Its signs give
the original mass alternative or a crossing alternative on the Fourier
image, without requiring a transformed polynomial face formula.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The diagonal weight retains the residual X-axis exponent. -/
theorem diagonal_x_factor_vDeg
    (P : A1 ℂ) (a k : ℕ) (lam α : ℂ) (hlam : lam ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    vDeg 1 1 P.1 = ((a+k : ℕ) : ℤ) := by
  have hX : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (0 : Fin 2)
  have hY : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (1 : Fin 2)
  have hshape : (leadingForm 1 1 P.1).IsWeightedHomogeneous (wt 1 1) ((a+k : ℕ) : ℤ) := by
    rw [hf]
    simpa [nsmul_eq_mul,mul_assoc] using ((hX.pow a).mul ((hY.sub (hX.C_mul α)).pow k)).C_mul lam
  have hc := positive_binomial_face_cut P 1 a k lam α (by simpa using hf)
  norm_num at hc
  have hcutne : cutPoly 1 1 P.1 ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero k (X_sub_C_ne_zero α))
  have hne : leadingForm 1 1 P.1 ≠ 0 := by
    intro hz; apply hcutne; simp [cutPoly,hz]
  have hhom : (leadingForm 1 1 P.1).IsWeightedHomogeneous (wt 1 1) (vDeg 1 1 P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 1) (n := vDeg 1 1 P.1)
  exact MvPolynomial.IsWeightedHomogeneous.inj_right hne hhom hshape

/-- A root multiplicity exceeding the axis exponent gives mass at least ten. -/
theorem diagonal_x_factor_mass_ge_ten
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a k : ℕ) (hak : a<k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    10 ≤ mass P.1 := by
  have hw := diagonal_x_factor_vDeg P a k lam α hlam hf
  have hp : 0<vDeg 1 1 P.1 := by rw [hw]; omega
  have hd := totalDeg_eq_vDeg_one_one P hp
  have hlarge := hdegree P Q hpair
  have hc := positive_binomial_face_cut P 1 a k lam α (by simpa using hf)
  norm_num at hc
  have hne : cutPoly 1 1 P.1 ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero k (X_sub_C_ne_zero α))
  have hdiv : (X-C α)^k ∣ cutPoly 1 1 P.1 := by rw [hc]; exact dvd_mul_left _ _
  have ht := Dixmier.pow_dvd_imp_lt_termCount hne hα hdiv
  have hm := cutPoly_termCount_le_mass P 1 1 (by norm_num)
  omega

/-- Every nonzero one-root face with a residual X-axis factor satisfies the
original-or-Fourier case alternative. -/
theorem preliminary_diagonal_x_factor_complete_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a k : ℕ) (hk : 1 ≤ k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  by_cases hpos : a<k
  · exact Or.inl (Or.inr (Or.inl (diagonal_x_factor_mass_ge_ten hdegree P Q hpair
      a k hpos lam α hlam hα hf)))
  · have hw := diagonal_x_factor_vDeg P a k lam α hlam hf
    obtain ⟨hp,hlast⟩ := positive_binomial_top_face_point P 1 a k lam α hlam
      (by simpa using hw) (by simpa using hf)
    have hFmem := fourier_diagonal_point_mem P (expo a k) hp
    have hFfirst : ∀ d ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support, d 0 ≤ k := by
      intro d hd
      have hpre := fourier_diagonal_point_preimage P d hd
      have hb := hlast (expo (d 1) (d 0)) hpre
      simpa [expo] using hb
    have hmem : expo k a ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support := by
      simpa [expo] using hFmem
    have hpairF := isCounterexamplePair_fourier P Q hpair
    have hn := preliminary_diagonal_first_point_grade_ne_zero hsource
      (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) hpairF k a (by omega) hmem hFfirst
    have hneg : k<a := by simp [grade,expo] at hn; omega
    have hc := preliminary_diagonal_negative_first_point_caseAlternative hsource
      (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) hpairF k a (by omega) hneg hmem hFfirst
    exact Or.inr (by simpa only [fourier_eq_algHom] using hc)

end Dixmier.Weyl
