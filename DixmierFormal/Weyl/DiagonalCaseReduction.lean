/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DiagonalXFactorDispatch
public import DixmierFormal.Weyl.CompleteDiagonalMonomialCases

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Reduction of the universal case map to two finite roots

The constant and single-factor diagonal branches satisfy the case map,
including a zero finite root. Only the two-distinct-root factorization
remains, with its residual axis exponent explicitly retained.
-/
namespace Dixmier.Weyl

/-- The complete single-factor branch includes the zero-root monomial case. -/
theorem preliminary_diagonal_single_factor_complete_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a k : ℕ) (hk : 1 ≤ k) (lam α : ℂ) (hlam : lam ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  by_cases hα : α=0
  · subst α
    apply preliminary_diagonal_monomial_complete_caseSplit hsource hdegree P Q hpair lam a k hlam
    simpa using hf
  · exact preliminary_diagonal_x_factor_complete_caseSplit hsource hdegree P Q hpair
      a k hk lam α hlam hα hf

/-- Every counterexample satisfies the case map or has the exact remaining
three-factor diagonal shape, with two distinct finite roots. -/
theorem preliminary_caseSplit_or_two_root_residual
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    (CaseAlternative P.1 ∨ CaseAlternative (fourier P.1)) ∨
    (∃ (lam α β : ℂ) (a u v : ℕ), lam ≠ 0 ∧ α ≠ β ∧ 1 ≤ u ∧ 1 ≤ v ∧
      leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
        (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^u *
        (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0)^v) := by
  rcases preliminary_diagonal_face_classification hsource P Q hpair with
    ⟨lam,a,hlam,ha,hf⟩ | ⟨lam,α,a,k,hlam,hk,hf⟩ | htwo
  · exact Or.inl (preliminary_diagonal_monomial_complete_caseSplit hsource hdegree
      P Q hpair lam a 0 hlam (by simpa using hf))
  · exact Or.inl (preliminary_diagonal_single_factor_complete_caseSplit hsource hdegree
      P Q hpair a k hk lam α hlam hf)
  · exact Or.inr htwo

end Dixmier.Weyl
