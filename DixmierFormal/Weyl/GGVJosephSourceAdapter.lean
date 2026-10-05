/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVTwoBracketDivisionAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Source-faithful Joseph interfaces for the preliminary GGV companion

G13 Section 4 uses Joseph Corollary 3.5 to obtain a nonzero first
bracket with vanishing second bracket. It then uses Joseph Lemma 2.2
to obtain a homogeneous fixed point. These two imported existence
claims are separated here. Neither is proved by this file.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The two-bracket operator witness used in G13 Section 4. -/
def GGVJosephTwoBracketInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
    IsDirection ρ σ →
    ∃ R : A1 ℂ,
      R ∈ Algebra.adjoin ℂ {P, Q} ∧
      poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) ≠ 0 ∧
      poisson (leadingForm ρ σ P.1)
        (poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1)) = 0

/-- Joseph Lemma 2.2 followed by GGV's polynomiality step, restricted
to the exact polynomial Weyl pair and a generated-algebra witness.
The source's intermediate fixed point lives in a Laurent symbol algebra;
requesting a polynomial result for arbitrary homogeneous `f,g` would
be stronger than the application recorded in G13 Section 4. -/
def GGVJosephFixedPointInput : Prop :=
  ∀ P Q R : A1 ℂ, IsCounterexamplePair P Q →
    R ∈ Algebra.adjoin ℂ {P, Q} →
    ∀ ρ σ : ℤ, IsDirection ρ σ →
    poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) ≠ 0 →
    poisson (leadingForm ρ σ P.1)
      (poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1)) = 0 →
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ + σ) ∧
      poisson (leadingForm ρ σ P.1) F = leadingForm ρ σ P.1

/-- The two Joseph source obligations give the preliminary companion
for exact counterexample pairs, with no restriction on the mate. -/
theorem ggv_preliminary_companion_of_joseph_inputs
    (htwo : GGVJosephTwoBracketInput)
    (hfixed : GGVJosephFixedPointInput) :
    GGVPreliminaryCompanionInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨R, hmem, hbr, hsecond⟩ := htwo P Q hpair ρ σ hdir
  exact hfixed P Q R hpair hmem ρ σ hdir hbr hsecond

theorem ggv_companion_of_joseph_inputs
    (hpower : GGVProperPowerInput)
    (htwo : GGVJosephTwoBracketInput)
    (hfixed : GGVJosephFixedPointInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ,
      IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
        IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_source_inputs hpower
    (ggv_preliminary_companion_of_joseph_inputs htwo hfixed)

end Dixmier.Weyl
