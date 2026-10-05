/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveDescentInvariant

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite positive-face shear descent

Exact polynomial root shears preserve the highest face point. Every
nonterminal step strictly decreases its positive integer slope.
-/
namespace Dixmier.Weyl

/-- A weighted monomial with nonzero coefficient has singleton support. -/
theorem weighted_monomial_support (lam : ℂ) (hlam : lam ≠ 0) (a b : ℕ) :
    (MvPolynomial.C lam * MvPolynomial.X (0 : Fin 2)^a * MvPolynomial.X 1^b).support =
      {expo a b} := by
  have hm : MvPolynomial.C lam * MvPolynomial.X (0 : Fin 2)^a * MvPolynomial.X 1^b =
      MvPolynomial.monomial (expo a b) lam := by
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, ← MvPolynomial.monomial_add_single]
    rfl
  rw [hm,MvPolynomial.support_monomial]
  simp [hlam]

/-- Shearing the next face retains the singleton's top point. -/
theorem preliminary_positive_descent_shear_step
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 (σ : ℤ) P.1).support, d = expo a b)
    (hbad : ∃ d ∈ (symbol P.1).support, a+b < d 0+d 1) :
    ∃ (τ : ℕ) (R S : A1 ℂ), 1 < τ ∧ τ < σ ∧ IsCounterexamplePair R S ∧
      (leadingForm 1 (τ : ℤ) R.1).support = {expo a b} := by
  have hy := preliminary_positive_last_point_y_bound hsource P Q hpair σ a b hσ hmem
    (by intro d hd; rw [hunique d hd]) hb
  obtain ⟨τ,hτ,hsmall,hdir,hpoint⟩ :=
    preliminary_positive_singleton_next_integer_face hsource P Q hpair σ a b hσ hb
      hmem hunique hbad
  obtain ⟨lam,α,hlam,hα,hd,hf⟩ :=
    preliminary_positive_binomial_at_top_point hsource P Q hpair τ a b hτ hdir hpoint hy
  obtain ⟨R,S,hRS,hR,hmono⟩ := polynomial_root_shear_monomial_face P Q hpair τ a b lam α hd
    (positive_binomial_face_cut P τ a b lam α hf)
  refine ⟨τ,R,S,hτ,hsmall,hRS,?_⟩
  rw [hmono]
  exact weighted_monomial_support lam hlam a b

/-- An occupied support point and a bound on all support sums determine total degree. -/
theorem totalDeg_eq_of_support_sum_bound (P : A1 ℂ) (a b : ℕ)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hbound : ∀ d ∈ (symbol P.1).support, d 0+d 1 ≤ a+b) :
    totalDeg P.1 = a+b := by
  apply Nat.le_antisymm
  · change (symbol P.1).support.sup (fun e => e.sum (fun _ n => n)) ≤ a+b
    apply Finset.sup_le
    intro e he
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)]
    simpa [Fin.sum_univ_two] using hbound e he
  · have h := MvPolynomial.le_totalDegree hpoint
    rw [Finsupp.sum_fintype (expo a b) (fun _ n => n) (by simp)] at h
    simpa [totalDeg,expo,Fin.sum_univ_two] using h

/-- Positive singleton descent terminates at the retained total-degree endpoint.
The companion input is required for every intervening polynomial pair. -/
theorem preliminary_positive_singleton_finite_descent
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 (σ : ℤ) P.1).support, d = expo a b) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧ totalDeg R.1 = a+b := by
  classical
  induction σ using Nat.strong_induction_on generalizing P Q with
  | h σ ih =>
    by_cases hbad : ∃ d ∈ (symbol P.1).support, a+b < d 0+d 1
    · obtain ⟨τ,R,S,hτ,hsmall,hRS,hface⟩ :=
        preliminary_positive_descent_shear_step hsource P Q hpair σ a b hσ hb hmem hunique hbad
      exact ih τ hsmall R S hRS (by omega)
        (by rw [hface]; simp)
        (by intro d hd; simpa [hface] using hd)
    · refine ⟨P,Q,hpair,totalDeg_eq_of_support_sum_bound P a b
        (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).1 ?_⟩
      intro d hd
      by_contra hn
      exact hbad ⟨d,hd,by omega⟩

end Dixmier.Weyl
