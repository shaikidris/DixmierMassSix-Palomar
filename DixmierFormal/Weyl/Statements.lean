/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Inputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Frozen statements of the Weyl-algebra results

These are the statements of the manuscript's generation theorem, pure-power face exclusion and
the two crossing lemmas, in the operator model of `DixmierFormal.Weyl.Defs`. The conditional
complex theorems (`GGVInputs → ...`) are proved in `DixmierFormal.Weyl`; the pending library
retains the unconditional and arbitrary-field targets as explicit unfinished contracts.
-/

namespace Dixmier.Statement

open Weyl MvPolynomial

/-- Mass-six generation: for any field `K` of characteristic zero, `[Q, P] = 1` and
`m(P) ≤ 6` imply `K⟨P, Q⟩ = A₁(K)`. -/
def MassSixGeneration.{u} : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (P Q : A1 K),
    Q * P - P * Q = 1 → mass P.1 ≤ 6 → Algebra.adjoin K {P, Q} = ⊤

/-- Pure-power face exclusion: for integers `q ≥ 2`, `s ≥ 0` with `ρ = (qs + 1)/(q - 1)`
integral, `p` prime and `α μ ≠ 0`, no counterexample pair has
`ℓ_{ρ,-s}(P) = μ x^p (1 + α x^s y^ρ)^{pq}`. -/
def PurePowerFaceExclusion : Prop :=
  ∀ (q s ρ p : ℕ) (α μ : ℂ), 2 ≤ q → (q - 1) * ρ = q * s + 1 → p.Prime → α ≠ 0 → μ ≠ 0 →
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      leadingForm ρ (-(s : ℤ)) P.1 ≠
        C μ * X 0 ^ p * (1 + C α * X 0 ^ s * X 1 ^ ρ) ^ (p * q)

/-- Negative crossing: a counterexample pair with `m(P) ≤ 6` has no strict crossing in a
direction `(ρ, -s)` with coprime integers `ρ > s ≥ 1`. -/
def NegativeCrossingExclusion : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → mass P.1 ≤ 6 →
    ∀ ρ s : ℕ, 1 ≤ s → s < ρ → Nat.Coprime ρ s → ¬ IsStrictCrossing ρ (-(s : ℤ)) P.1

/-- Horizontal crossing: a counterexample pair with `m(P) ≤ 6` has no strict crossing in the
direction `(1, 0)`. -/
def HorizontalCrossingExclusion : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → mass P.1 ≤ 6 → ¬ IsStrictCrossing 1 0 P.1

end Dixmier.Statement
