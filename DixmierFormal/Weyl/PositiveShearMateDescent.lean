/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveShearFiniteDescent
public import DixmierFormal.Weyl.PolynomialShearTopRow

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite positive descent retaining the unrestricted mate's top row

The same exact shears act on both members. The first endpoint determines
the terminal total degree; the mate's differential-order bound and its
occupied top row are retained through every step.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem preliminary_positive_descent_shear_step_with_mate_row
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b c d : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b)
    (hbad : ∃ e ∈ (symbol P.1).support, a+b < e 0+e 1)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support) :
    ∃ (τ : ℕ) (R S : A1 ℂ), 1 < τ ∧ τ < σ ∧ IsCounterexamplePair R S ∧
      (leadingForm 1 (τ : ℤ) R.1).support = {expo a b} ∧
      (∀ e ∈ (symbol S.1).support, e 1 ≤ d) ∧
      expo c d ∈ (symbol S.1).support := by
  have hy := preliminary_positive_last_point_y_bound hsource P Q hpair σ a b hσ hmem
    (by intro e he; rw [hunique e he]) hb
  obtain ⟨τ,hτ,hsmall,hdir,hpoint⟩ :=
    preliminary_positive_singleton_next_integer_face hsource P Q hpair σ a b hσ hb
      hmem hunique hbad
  obtain ⟨lam,α,hlam,_,hd,hf⟩ :=
    preliminary_positive_binomial_at_top_point hsource P Q hpair τ a b hτ hdir hpoint hy
  obtain ⟨R,S,hRS,hR,hS⟩ :=
    polynomial_monomial_cut_recovers_polynomial_counterexample τ α P Q hpair
  have hPne : P ≠ 0 := by
    intro hz
    have h := congrArg Subtype.val hpair.1
    rw [hz] at h
    simp at h
  have hdirection : IsDirection 1 (τ : ℤ) := ⟨by simp,by positivity⟩
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 (τ : ℤ) hdirection
  have hr := counterexample_vDeg_pos_all_directions R S hRS 1 (τ : ℤ) hdirection
  have ht := polynomial_monomial_cut_weight_and_translate P R τ α hPne hp hr hR
  have hcut : cutPoly 1 (τ : ℤ) R.1 = Polynomial.C lam * Polynomial.X^b := by
    rw [ht.2,positive_binomial_face_cut P τ a b lam α hf]
    simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,
      Polynomial.X_comp,Polynomial.C_comp]
    simp
  have hface := positive_face_eq_of_linear_power_cut R lam 0 τ a b
    (ht.1.trans hd) (by simpa using hcut)
  have hface' : leadingForm 1 (τ : ℤ) R.1 =
      MvPolynomial.C lam * MvPolynomial.X 0^a * MvPolynomial.X 1^b := by
    simpa using hface
  refine ⟨τ,R,S,hτ,hsmall,hRS,?_,?_,?_⟩
  · rw [hface']
    exact weighted_monomial_support lam hlam a b
  · exact (polynomial_cut_preserves_y_bound_and_top_row Q S 1 (τ : ℤ) α d
      hQbound hS).1
  · exact polynomial_cut_preserves_top_row_point Q S 1 (τ : ℤ) α c d
      hQbound hQpoint hS

theorem preliminary_positive_singleton_finite_descent_with_mate_row
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b c d : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧ totalDeg R.1 = a+b ∧
      expo a b ∈ (symbol R.1).support ∧
      (∀ e ∈ (symbol S.1).support, e 1 ≤ d) ∧
      expo c d ∈ (symbol S.1).support := by
  classical
  induction σ using Nat.strong_induction_on generalizing P Q with
  | h σ ih =>
    by_cases hbad : ∃ e ∈ (symbol P.1).support, a+b < e 0+e 1
    · obtain ⟨τ,R,S,hτ,hsmall,hRS,hface,hSbound,hSpoint⟩ :=
        preliminary_positive_descent_shear_step_with_mate_row hsource P Q hpair
          σ a b c d hσ hb hmem hunique hbad hQbound hQpoint
      exact ih τ hsmall R S hRS (by omega)
        (by rw [hface]; simp) (by intro e he; simpa [hface] using he)
        hSbound hSpoint
    · refine ⟨P,Q,hpair,totalDeg_eq_of_support_sum_bound P a b
        (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).1 ?_,
        (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).1,hQbound,hQpoint⟩
      intro e he
      by_contra hn
      exact hbad ⟨e,he,by omega⟩

end Dixmier.Weyl
