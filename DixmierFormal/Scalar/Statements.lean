/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Frozen statements of the scalar results

Each declaration is a `Prop` stating one scalar result of the manuscript literally.
Proofs live elsewhere and are connected by `DixmierFormal.Main`; the audit library checks the
types.  This module is part of the frozen statement contract (`FROZEN.sha256`).

The mapping to paper numbering is kept in `THEOREM_MAP.md`, not in declaration names.
-/

namespace Dixmier.Statement

open Polynomial

/-- Sparse multiplicity bound: every nonzero root of a nonzero polynomial with `t` terms has
multiplicity at most `t - 1`. -/
def SparseRootBound : Prop :=
  ∀ (S : ℂ[X]) (α : ℂ), S ≠ 0 → α ≠ 0 → rootMultiplicity α S ≤ termCount S - 1

/-- Two fourth-order roots of a six-term polynomial: with constant coefficient one and primitive
exponent support, two distinct nonzero roots of multiplicity at least four are the only such
roots, and after a nonzero scaling of the variable the polynomial has real coefficients and these
roots become nonreal complex conjugates on the unit circle. -/
def SixTermTwoFourthOrderRoots : Prop :=
  ∀ (S : ℂ[X]) (α β : ℂ), termCount S = 6 → S.coeff 0 = 1 → HasPrimitiveSupport S →
    α ≠ 0 → β ≠ 0 → α ≠ β → 4 ≤ rootMultiplicity α S → 4 ≤ rootMultiplicity β S →
    (∀ γ : ℂ, γ ≠ 0 → 4 ≤ rootMultiplicity γ S → γ = α ∨ γ = β) ∧
    ∃ c : ℂ, c ≠ 0 ∧ (∀ n : ℕ, ((S.comp (C c * X)).coeff n).im = 0) ∧
      (α / c).im ≠ 0 ∧ β / c = (starRingEnd ℂ) (α / c) ∧ Complex.normSq (α / c) = 1

/-- A five-term polynomial with nonzero constant coefficient and primitive exponent support has
at most one nonzero root of multiplicity at least four. -/
def FiveTermUniqueFourthOrderRoot : Prop :=
  ∀ (S : ℂ[X]), termCount S = 5 → HasPrimitiveSupport S →
    ∀ α β : ℂ, α ≠ 0 → β ≠ 0 → 4 ≤ rootMultiplicity α S → 4 ≤ rootMultiplicity β S → α = β

/-- Scalar classification: for integers `ρ > s ≥ 1` and polynomials `r, f` over `ℂ` with `r`
nonconstant, `r(0) = 1` and the companion equation, `t(r²) ≤ 6` forces `ρ = 2s + 1`,
`r = (1 - λ w)²`, `f = λ w - 1` for some `λ ≠ 0`; in particular `r²` has exactly five terms. -/
def ScalarClassification : Prop :=
  ∀ (ρ s : ℤ) (r f : ℂ[X]), 1 ≤ s → s < ρ → 0 < r.natDegree → r.eval 0 = 1 →
    CompanionEq ρ s r f → termCount (r ^ 2) ≤ 6 →
    ρ = 2 * s + 1 ∧ (∃ lam : ℂ, lam ≠ 0 ∧ r = (1 - C lam * X) ^ 2 ∧ f = C lam * X - 1) ∧
      termCount (r ^ 2) = 5

end Dixmier.Statement
