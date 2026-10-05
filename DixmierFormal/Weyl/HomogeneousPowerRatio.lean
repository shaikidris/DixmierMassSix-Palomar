/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.BivariateRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Power relation for commuting homogeneous faces

The Poisson equation and weighted Euler identity supply two cleared
logarithmic-derivative identities. The bivariate constant-ratio theorem
converts them to an actual power relation without a monicity assumption.
The further common-power factorization remains separate.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The general positive-weight homogeneous Poisson relation, with no
monicity or support-shape assumption. The two cleared derivative identities
force a constant ratio of the corresponding powers. -/
theorem homogeneous_poisson_power_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (ρ σ : ℤ) (m ω : ℕ)
    (hm : 0 < m) (hω : 0 < ω) (hB0 : B ≠ 0) (hR0 : R ≠ 0)
    (hB : B.IsWeightedHomogeneous (wt ρ σ) ω)
    (hR : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hbr : poisson B R = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ B ^ m = MvPolynomial.C c * R ^ ω := by
  have hder := homogeneous_poisson_derivative_identities B R ρ σ ω m hB hR hbr
  have hpow := power_cross_derivative_identities B R m ω hm hω
    (by simpa only [Int.cast_natCast] using hder)
  obtain ⟨c, hc⟩ := bivariate_cross_derivatives_constant
    (B ^ m) (R ^ ω) (pow_ne_zero _ hR0) hpow.1 hpow.2
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz] at hc
  simp at hc
  exact hB0 hc.1

/-- A source-level Poisson power relation when a power of the first face
has a coefficient equal to one in the `x`-polynomial presentation. -/
theorem homogeneous_poisson_power_ratio_of_monic_x
    (B R : MvPolynomial (Fin 2) ℂ) (ρ σ : ℤ) (m ω : ℕ)
    (hm : 0 < m) (hω : 0 < ω)
    (hB : B.IsWeightedHomogeneous (wt ρ σ) ω)
    (hR : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hbr : poisson B R = 0)
    (n : ℕ)
    (hmonic : (MvPolynomial.finSuccEquiv ℂ 1 (R ^ ω)).coeff n = 1) :
    ∃ c : ℂ, B ^ m = MvPolynomial.C c * R ^ ω := by
  have hder := homogeneous_poisson_derivative_identities B R ρ σ ω m
    (by simpa only [Int.cast_natCast] using hB)
    (by simpa only [Int.cast_natCast] using hR) hbr
  have hpow := power_cross_derivative_identities B R m ω hm hω
    (by simpa only [Int.cast_natCast] using hder)
  exact bivariate_cross_derivatives_constant_of_monic_x (B ^ m) (R ^ ω) n
    hmonic hpow.1 hpow.2

end Dixmier.Weyl
