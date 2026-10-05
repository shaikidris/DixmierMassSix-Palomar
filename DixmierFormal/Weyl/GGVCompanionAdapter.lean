/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Inputs
public import DixmierFormal.Weyl.CompanionPowerCancellation
public import DixmierFormal.Weyl.GGVPositiveWeight
public import DixmierFormal.Weyl.Validation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Source-shaped decomposition of GGV Proposition 2.6

The published proof imports proper-power rigidity and a preliminary
homogeneous companion. This file proves that these two source obligations
imply the exact frozen `GGVInputs.companion` field. Neither obligation is
asserted as an axiom or proved here.
-/

namespace Dixmier.Weyl

open MvPolynomial

private theorem weightedDegree_eq_vDeg_of_pos
    (T : A1 ℂ) (ρ σ : ℤ) (hpos : 0 < vDeg ρ σ T.1) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T.1) =
      (vDeg ρ σ T.1 : WithBot ℤ) := by
  cases h : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T.1) with
  | bot => simp [vDeg, h] at hpos
  | coe m => simp [vDeg, h]

/-- Translate the nonzero leading-bracket assertion of G13 Theorem 4.1
from PBW operators to the exact Poisson identity used by G24. The source
bracket is expressed as the component at the predicted commutator weight. -/
theorem preliminary_companion_symbol_of_operator
    (P F : A1 ℂ) (ρ σ : ℤ)
    (hsum : 0 < ρ + σ)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hFdeg : vDeg ρ σ F.1 = ρ + σ)
    (hFhom : IsWeightedHomogeneous (wt ρ σ) (symbol F.1) (ρ + σ))
    (hbr : MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
      (vDeg ρ σ P.1 + vDeg ρ σ F.1 - (ρ + σ))
      (symbol ((P * F - F * P : A1 ℂ) : Module.End ℂ (Polynomial ℂ))) =
      leadingForm ρ σ P.1) :
    poisson (leadingForm ρ σ P.1) (symbol F.1) = leadingForm ρ σ P.1 := by
  have hPweight := weightedDegree_eq_vDeg_of_pos P ρ σ hPpos
  have hFpos : 0 < vDeg ρ σ F.1 := by omega
  have hFweight := weightedDegree_eq_vDeg_of_pos F ρ σ hFpos
  have htop := symbol_commutator_top_component P F ρ σ
    (vDeg ρ σ P.1) (vDeg ρ σ F.1) hsum hPweight hFweight
  rw [hFdeg, weightedHomogeneousComponent_eq_self (w := wt ρ σ) hFhom] at htop
  exact htop.symm.trans (by simpa [hFdeg] using hbr)

/-- The proper-power half of GGV Proposition 2.6, as imported there from
Han--Tan. The witness is a homogeneous *symbol*, with the PBW map already
eliminated from the statement. -/
def GGVProperPowerInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k

/-- The preliminary companion half, imported by GGV from their earlier
Theorem 4.1. Its conclusion is deliberately about the whole leading form,
before cancellation of the proper power. -/
def GGVPreliminaryCompanionInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
    ∃ F : MvPolynomial (Fin 2) ℂ,
      IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
      poisson (leadingForm ρ σ P.1) F = leadingForm ρ σ P.1

/-- G13 Theorem 4.1 in operator/PBW form, restricted to the exact
counterexample pairs needed here. Its bracket is the selected component
at the predicted weight, matching the source's `[P,F]_{ρ,σ}`. -/
def GGVOperatorPreliminaryInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
    ∃ F : A1 ℂ,
      vDeg ρ σ F.1 = ρ + σ ∧
      IsWeightedHomogeneous (wt ρ σ) (symbol F.1) (ρ + σ) ∧
      MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ P.1 + vDeg ρ σ F.1 - (ρ + σ))
        (symbol ((P * F - F * P : A1 ℂ) : Module.End ℂ (Polynomial ℂ))) =
        leadingForm ρ σ P.1

/-- The operator-level G13 input implies the symbol-level preliminary
companion input; positivity is discharged internally from opposite grades. -/
theorem ggv_preliminary_companion_of_operator_input
    (hsource : GGVOperatorPreliminaryInput) : GGVPreliminaryCompanionInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨F, hFdeg, hFhom, hbr⟩ := hsource P Q hpair ρ σ hdir
  exact ⟨symbol F.1, hFhom,
    preliminary_companion_symbol_of_operator P F ρ σ hdir.2
      (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)
      hFdeg hFhom hbr⟩

/-- The source-shaped proper-power and preliminary-companion statements
assemble into the exact frozen companion field. -/
theorem ggv_companion_of_source_inputs
    (hpower : GGVProperPowerInput)
    (hprelim : GGVPreliminaryCompanionInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R := by
  intro P Q hpair ρ σ hdir
  obtain ⟨μ, k, R, m, hμ, hk, hR, hRhom, hface⟩ := hpower P Q hpair ρ σ hdir
  obtain ⟨F, hFhom, hbr⟩ := hprelim P Q hpair ρ σ hdir
  refine ⟨μ, k, R, C (k : ℂ) * F, m, hμ, hk, hR, hRhom, ?_, hface, ?_⟩
  · exact hFhom.C_mul (k : ℂ)
  · apply poisson_power_companion_cancel R F μ k hμ (by omega) hR
    rw [← hface]
    exact hbr

/-- Exact source-to-contract route, with the G13 operator witness retained
until the final PBW-symbol translation. -/
theorem ggv_companion_of_operator_source_inputs
    (hpower : GGVProperPowerInput)
    (hoperator : GGVOperatorPreliminaryInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_source_inputs hpower
    (ggv_preliminary_companion_of_operator_input hoperator)

end Dixmier.Weyl
