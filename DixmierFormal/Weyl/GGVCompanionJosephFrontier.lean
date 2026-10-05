/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.JosephInitialWitness
public import DixmierFormal.Weyl.NegativeCrossingProperPower
public import DixmierFormal.Weyl.PoissonTwoBracketPolynomiality

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Remaining Joseph frontier for the GGV companion field

The proper-power half of GGV Proposition 2.6 is now proved globally.
The Joseph two-bracket witness is proved for every counterexample direction.
The homogeneous two-bracket polynomiality theorem proves the fixed-point
input. Together these results discharge the exact companion field.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem ggv_companion_of_joseph_only
    (htwo : GGVJosephTwoBracketInput)
    (hfixed : GGVJosephFixedPointInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_joseph_inputs
    ggv_proper_power_input_proved htwo hfixed

theorem ggv_companion_of_fixed_point_only
    (hfixed : GGVJosephFixedPointInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_joseph_only ggv_joseph_two_bracket_proved hfixed

theorem ggv_companion_of_positive_bracket_fixed_point
    (hpositive : GGVJosephPositiveBracketFixedPointInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_fixed_point_only
    (ggv_joseph_fixed_point_of_positive_bracket hpositive)

theorem ggv_companion_of_large_witness_fixed_point
    (hlarge : GGVJosephLargeWitnessFixedPointInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_fixed_point_only
    (ggv_joseph_fixed_point_of_large_witness hlarge)

theorem ggv_preliminary_companion_proved : GGVPreliminaryCompanionInput :=
  ggv_preliminary_companion_of_joseph_inputs
    ggv_joseph_two_bracket_proved ggv_joseph_fixed_point_proved

theorem ggv_companion_proved :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_source_inputs ggv_proper_power_input_proved
    ggv_preliminary_companion_proved

end Dixmier.Weyl
