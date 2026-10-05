/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Imported structural inputs (frozen contract)

`GGVInputs` collects, as one `Prop`-valued hypothesis, the published results of Guccione,
Guccione and Valqui used by the mass-six theorem.  Nothing here is proved: the conditional
theorems take `GGVInputs` as an explicit argument, so `#print axioms` stays clean and the
dependence on the literature is visible in every statement.

Every field is quantified over counterexample pairs only, so each field is no stronger than its
source statement (several sources hold for all exact pairs). Provenance, versions and the source
interfaces are tracked in `FORMALIZATION_TRACKER.md`; review each field against its source before
relying on a conditional theorem.  The warning of the formalization plan applies: a field stated
too strongly could contradict the existence of counterexample pairs and make the conditional
theorems vacuous, and Lean cannot detect this.

Conventions: `[Q, P] = 1` as in the manuscript (G24 uses `[P, Q] = 1`; replacing the mate by its
negative reconciles the two without changing `P`).  Sources: [G13] arXiv:1111.6100v3,
[G24] arXiv:2402.11135v1.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The published structural inputs of the mass-six theorem. -/
structure GGVInputs : Prop where
  /-- [G24, Proposition 1.2]: the maximal and minimal grades of a counterexample member have
  opposite signs. -/
  grades_opposite : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
    (∃ d ∈ (symbol P.1).support, 0 < grade d) ∧ (∃ d ∈ (symbol P.1).support, grade d < 0)
  /-- [G24, Proposition 2.6], with the leading bracket written as the Poisson bracket of the
  homogeneous symbols: in every positive-sum direction, `ℓ(P) = μ R^k` with `k ≥ 2` and a
  homogeneous companion `F` of weight `ρ + σ` with `{R, F} = R`. -/
  companion : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
    ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
      IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
      leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R
  /-- [G24, Remark 3.3, Proposition 4.1 and the proof of Theorem 4.2], as collected in the
  manuscript's case reduction: after at most the Fourier exchange, a strict crossing face with
  `ρ > 0, -ρ < σ ≤ 0`, or mass at least ten, or a two-root total-degree leading symbol. -/
  caseSplit : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1)
  /-- [G13, Corollary 7.4]: the degree gcd of every counterexample pair exceeds fifteen. -/
  degreeBound : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
    15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)
  /-- [G13, Propositions 5.3 and 5.6] combined at the symbol level for a polynomial pair: the
  maximum-root cut (in `A₁^{(ρ)}`, since `lcm(1, ρ) = ρ`) under hypotheses (a)–(f) of 5.3
  produces the ending point `(u + (v₀ - M) σ / ρ, M)`, where `(u, v₀)` is the starting point and
  `M` the maximal root multiplicity of the cut polynomial; by 5.6, after division by the
  reduced denominator `d` of `v(Q)/v(P)` it is not `(h - 1/ρ, h)` with `h ≥ 2`.  Hypothesis
  (d), `[P, Q]_{ρ,σ} = 0`, is written as `ρ + σ < v(P) + v(Q)`, which is equivalent for an
  exact pair by [G13, Definitions 2.1–2.2]. -/
  cutCorner : ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (u v₀ n d h : ℕ), IsCounterexamplePair P Q →
    IsDirection ρ σ → 0 < ρ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
    0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 → ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1 →
    ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
    (∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) →
    (∃ e ∈ (leadingForm ρ σ Q.1).support, grade e < 0) →
    expo u v₀ ∈ (leadingForm ρ σ P.1).support →
    (∀ e ∈ (leadingForm ρ σ P.1).support, grade e ≤ grade (expo u v₀)) →
    vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
    ¬ (((u : ℚ) + ((v₀ : ℚ) - maxRootMult (cutPoly ρ σ P.1)) * σ / ρ) / d = h - 1 / ρ ∧
        (maxRootMult (cutPoly ρ σ P.1) : ℚ) / d = h)
  /-- [G13, Proposition 5.6] for a polynomial pair (`l = 1`): with hypotheses (a), (b), (c),
  (e) of 5.3, `σ ≤ 0`, and reduced ratio `v(Q)/v(P) = n/d` with `n, d > 1`, the ending point
  `(a, b)` (the face point of minimal grade) satisfies `(a, b)/d ≠ (h - 1, h)` for `h ≥ 2`. -/
  corner : ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ), IsCounterexamplePair P Q →
    IsDirection ρ σ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
    0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 →
    ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
    expo a b ∈ (leadingForm ρ σ P.1).support →
    (∀ e ∈ (leadingForm ρ σ P.1).support, grade (expo a b) ≤ grade e) →
    vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
    ¬ ((a : ℚ) / d = h - 1 ∧ (b : ℚ) / d = h)

end Dixmier.Weyl
