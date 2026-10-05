/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DiagonalYFactorMass
public import DixmierFormal.Weyl.DiagonalHorizontalEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Complete one-root dispatch with a residual Y-axis factor

The lowest occupied cut coefficient determines the rightmost diagonal
endpoint. Its negative grade gives crossing and its positive grade gives
the mass-ten alternative; the exact endpoint cannot have zero grade.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The residual axis factor fixes the rightmost occupied diagonal point. -/
theorem diagonal_y_factor_first_face_point
    (P : A1 ℂ) (b k : ℕ) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    expo k b ∈ (leadingForm 1 1 P.1).support ∧
      ∀ d ∈ (leadingForm 1 1 P.1).support, d 0 ≤ k := by
  have hshape : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C (0 : ℂ) * MvPolynomial.X 0)^b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k := by simpa using hf
  have hw := twoRoot_vDeg_eq_exponent_sum P lam 0 α b k hlam hshape
  have hc : cutPoly 1 1 P.1 = X^b * (C lam * (X-C α)^k) := by
    rw [twoRoot_cutPoly P lam 0 α b k hshape]
    simp only [map_zero,sub_zero]
    ring
  have hcoeff : (cutPoly 1 1 P.1).coeff b ≠ 0 := by
    rw [hc]
    have hz := coeff_X_pow_mul (C lam * (X-C α)^k) b 0
    simp only [zero_add] at hz
    rw [hz]
    simp [coeff_zero_eq_eval_zero,hlam,hα]
  constructor
  · rw [MvPolynomial.mem_support_iff]
    rw [← cutPoly_coeff_at_face_point P 1 1 k b (by norm_num)
      (by rw [hw]; push_cast; ring)]
    exact hcoeff
  · intro d hd
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
    have hwt := (polynomialFace_point_source_data P 1 1 i j hd).2
    have hnz : (cutPoly 1 1 P.1).coeff j ≠ 0 := by
      rw [cutPoly_coeff_at_face_point P 1 1 i j (by norm_num) (by simpa using hwt)]
      exact MvPolynomial.mem_support_iff.mp hd
    have hj : b ≤ j := by
      by_contra hnot
      rw [hc,coeff_X_pow_mul',if_neg (by omega)] at hnz
      exact hnz rfl
    rw [hw] at hwt
    norm_num at hwt
    simp only [expo]
    norm_num
    omega

/-- Every nonzero one-root face with a residual Y-axis factor satisfies the
original member's case alternative. -/
theorem preliminary_diagonal_y_factor_complete_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (b k : ℕ) (hk : 1 ≤ k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    CaseAlternative P := by
  obtain ⟨hm,hfirst⟩ := diagonal_y_factor_first_face_point P b k lam α hlam hα hf
  by_cases hpos : b<k
  · exact diagonal_y_factor_caseAlternative hdegree P Q hpair b k hpos lam α hlam hα hf
  · have hn := preliminary_diagonal_first_point_grade_ne_zero hsource P Q hpair
      k b (by omega) hm hfirst
    have hneg : k<b := by
      simp [grade,expo] at hn
      omega
    exact preliminary_diagonal_negative_first_point_caseAlternative hsource P Q hpair
      k b (by omega) hneg hm hfirst

end Dixmier.Weyl
