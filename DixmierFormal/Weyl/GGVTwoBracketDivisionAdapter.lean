/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonHomogeneousWeight
public import DixmierFormal.Weyl.GGVCompanionAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Sufficient two-bracket division interface to the GGV preliminary companion

The two-bracket witness and polynomial divisibility remain explicit
premises. This file proves that they imply the existing GGV companion
contract, with the correct signed Newton weight and unrestricted mate.
The divisibility premise is a sufficient condition used by this adapter;
it is not asserted by GGV Section 4 or Joseph's cited Lemma 2.2.
Discharging the source contract requires a proof of Joseph's actual
fixed-point step or an independent proof of this stronger divisibility.
-/

namespace Dixmier.Weyl

open MvPolynomial

def GGVTwoBracketDivisionInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
    IsDirection ρ σ →
    ∃ R : A1 ℂ, ∃ F : MvPolynomial (Fin 2) ℂ,
      poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) ≠ 0 ∧
      poisson (leadingForm ρ σ P.1)
        (poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1)) = 0 ∧
      poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) * F =
        leadingForm ρ σ P.1 * leadingForm ρ σ R.1

theorem ggv_preliminary_companion_of_two_bracket_division
    (hsource : GGVTwoBracketDivisionInput) :
    GGVPreliminaryCompanionInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨R, F, hbr, hsecond, hdiv⟩ := hsource P Q hpair ρ σ hdir
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hRhom : (leadingForm ρ σ R.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ R.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol R.1) (w := wt ρ σ) (n := vDeg ρ σ R.1)
  obtain ⟨hfixed, hFhom⟩ :=
    poisson_fixed_point_of_two_brackets_and_division
      ρ σ (vDeg ρ σ P.1) (vDeg ρ σ R.1)
      (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) F
      hPhom hRhom hbr hsecond hdiv
  exact ⟨F, hFhom, hfixed⟩

/-- The two-bracket source condition and the separate proper-power
input yield the exact companion field consumed by the mass-six proof. -/
theorem ggv_companion_of_two_bracket_division
    (hpower : GGVProperPowerInput)
    (hsource : GGVTwoBracketDivisionInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R := by
  exact ggv_companion_of_source_inputs hpower
    (ggv_preliminary_companion_of_two_bracket_division hsource)

end Dixmier.Weyl
