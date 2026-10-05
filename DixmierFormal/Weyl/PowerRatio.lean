/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.EulerPoisson

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Clearing logarithmic derivatives of homogeneous face powers

The Euler--Poisson identities imply that corresponding powers have the
same logarithmic derivatives. This is the denominator-free polynomial
identity preceding the paper's factor-order comparison.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

/-- A strictly positive weighted degree has a nonzero leading form. The
definition assigns degree zero to the zero operator, so positivity rules out
that exceptional case before applying the top-component support theorem. -/
theorem leadingForm_ne_zero_of_vDeg_pos
    (T : A1 ℂ) (ρ σ : ℤ)
    (hpos : 0 < vDeg ρ σ (T : Module.End ℂ ℂ[X])) :
    leadingForm ρ σ (T : Module.End ℂ ℂ[X]) ≠ 0 := by
  let d := MvPolynomial.weightedTotalDegree' (wt ρ σ)
    (symbol (T : Module.End ℂ ℂ[X]))
  have hdnot : d ≠ ⊥ := by
    intro hbot
    have hzero : vDeg ρ σ (T : Module.End ℂ ℂ[X]) = 0 := by
      simp [vDeg, d, hbot]
    omega
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hdnot
  have hv : vDeg ρ σ (T : Module.End ℂ ℂ[X]) = m := by
    change WithBot.unbotD 0 d = m
    rw [← hm]
    rfl
  have hdegree : d = (vDeg ρ σ (T : Module.End ℂ ℂ[X]) : WithBot ℤ) := by
    rw [hv]
    exact hm.symm
  exact weightedComponent_ne_zero_of_weightedTotalDegree_eq
    (wt ρ σ) (symbol (T : Module.End ℂ ℂ[X]))
    (vDeg ρ σ (T : Module.End ℂ ℂ[X])) hdegree

theorem cross_derivative_of_logarithmic_identity
    (B R : MvPolynomial (Fin 2) ℂ) (a b : ℕ) (i : Fin 2)
    (h : ((a + 1 : ℕ) : ℂ) • (R * pderiv i B) =
      ((b + 1 : ℕ) : ℂ) • (B * pderiv i R)) :
    R ^ (b + 1) * pderiv i (B ^ (a + 1)) =
      B ^ (a + 1) * pderiv i (R ^ (b + 1)) := by
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq] at h
  have hcast (n : ℕ) :
      (MvPolynomial.C (n : ℂ) : MvPolynomial (Fin 2) ℂ) = n := by
    exact map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) n
  rw [hcast (a + 1), hcast (b + 1)] at h
  simp only [MvPolynomial.pderiv_pow]
  rw [pow_succ R b, pow_succ B a]
  simp only [Nat.add_sub_cancel_right]
  linear_combination (B ^ a * R ^ b) * h

/-- Clearing the logarithmic derivatives for both variables yields the
polynomial identities asserting that `B^ρ/R^ω` has zero partial derivatives.
This theorem does not yet assert that the ratio is constant. -/
theorem power_cross_derivative_identities
    (B R : MvPolynomial (Fin 2) ℂ) (ρ ω : ℕ)
    (hρ : 0 < ρ) (hω : 0 < ω)
    (h : ((ρ : ℂ) • (R * pderiv 0 B) = (ω : ℂ) • (B * pderiv 0 R)) ∧
      ((ρ : ℂ) • (R * pderiv 1 B) = (ω : ℂ) • (B * pderiv 1 R))) :
    (R ^ ω * pderiv 0 (B ^ ρ) = B ^ ρ * pderiv 0 (R ^ ω)) ∧
      (R ^ ω * pderiv 1 (B ^ ρ) = B ^ ρ * pderiv 1 (R ^ ω)) := by
  cases ρ with
  | zero => omega
  | succ a =>
      cases ω with
      | zero => omega
      | succ b =>
          constructor
          · exact cross_derivative_of_logarithmic_identity B R a b 0 h.1
          · exact cross_derivative_of_logarithmic_identity B R a b 1 h.2

/-- The paper's exact crossing face supplies the two cleared derivative
identities for the genuine leading form of its Weyl mate. The remaining
constant-ratio and factor-order implications are separate obligations. -/
theorem crossingFace_mate_power_cross_derivatives
    (P Q : A1 ℂ) (μ α : ℂ) (p q ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hsρ : s < ρ) (hω : 0 < ω)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ *
        (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q) ^ p) :
    let R : MvPolynomial (Fin 2) ℂ :=
      X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q
    let B := leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])
    (R ^ ω * pderiv 0 (B ^ ρ) = B ^ ρ * pderiv 0 (R ^ ω)) ∧
      (R ^ ω * pderiv 1 (B ^ ρ) = B ^ ρ * pderiv 1 (R ^ ω)) := by
  dsimp
  exact power_cross_derivative_identities
    (leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]))
    (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q)
    ρ ω (Nat.zero_lt_of_lt hsρ) hω
    (crossingFace_mate_derivative_identities P Q μ α p q ρ s ω
      hμ hp hsρ hω hexact hPweight hQweight hPface)

end Dixmier.Weyl
