/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.SignedEuler

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Euler--Poisson derivative compatibility

For two signed-weight homogeneous symbols whose Poisson bracket vanishes,
weighted Euler identities identify the logarithmic derivatives needed for
the factor-order comparison in the pure-power mate argument.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

/-- The crossing-face base `x(1+α x^s y^ρ)^q` has signed weight `ρ`.
This discharges the homogeneous-base hypothesis used below for the paper's
actual face shape. -/
theorem crossingBase_isWeightedHomogeneous (α : ℂ) (q ρ s : ℕ) :
    (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q :
      MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      (wt ρ (-(s : ℤ))) ρ := by
  let w := wt (ρ : ℤ) (-(s : ℤ))
  have hx : (X 0 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous w ρ := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 0)
  have hy : (X 1 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous w (-(s : ℤ)) := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 1)
  have hmon : (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w 0 := by
    have h := (hx.pow s).mul (hy.pow ρ)
    convert h using 1
    simp
    ring
  have hinner : (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ :
      MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous w 0 := by
    exact (MvPolynomial.isWeightedHomogeneous_one ℂ w).add
      (by simpa only [mul_assoc] using hmon.C_mul α)
  have hpow : ((1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q :
      MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous w 0 := by
    simpa using hinner.pow q
  simpa [w] using hx.mul hpow

/-- The crossing base cannot vanish: its inner factor has constant value one
when `ρ>0`, independently of `α`, `s`, or the outer power. -/
theorem crossingBase_ne_zero (α : ℂ) (q ρ s : ℕ) (hρ : 0 < ρ) :
    (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q :
      MvPolynomial (Fin 2) ℂ) ≠ 0 := by
  have hinner : (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ :
      MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    intro h
    have heval := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) h
    simp [Nat.ne_of_gt hρ] at heval
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) (pow_ne_zero _ hinner)

theorem homogeneous_poisson_derivative_identities
    (B R : MvPolynomial (Fin 2) ℂ) (ρ σ ω m : ℤ)
    (hB : B.IsWeightedHomogeneous (wt ρ σ) ω)
    (hR : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hbr : poisson B R = 0) :
    ((m : ℂ) • (R * pderiv 0 B) = (ω : ℂ) • (B * pderiv 0 R)) ∧
      ((m : ℂ) • (R * pderiv 1 B) = (ω : ℂ) • (B * pderiv 1 R)) := by
  have hEB := signedWeightedEuler B ρ σ ω hB
  have hER := signedWeightedEuler R ρ σ m hR
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq] at hEB hER ⊢
  dsimp [poisson] at hbr
  constructor
  · linear_combination (pderiv 0 R) * hEB - (pderiv 0 B) * hER -
      (MvPolynomial.C (σ : ℂ) * X 1) * hbr
  · linear_combination (pderiv 1 R) * hEB - (pderiv 1 B) * hER +
      (MvPolynomial.C (ρ : ℂ) * X 0) * hbr

/-- For an exact Weyl pair with a pure-power leading face, the mate's actual
leading symbol satisfies the two derivative identities with the base face.
No bound is imposed on the mate's differential order or support. -/
theorem purePower_mate_derivative_identities
    (P Q : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (μ : ℂ) (p ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hsρ : s < ρ) (hω : 0 < ω) (hR : R ≠ 0)
    (hRhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ρ)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ * R ^ p) :
    let B := leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])
    ((ρ : ℂ) • (R * pderiv 0 B) = (ω : ℂ) • (B * pderiv 0 R)) ∧
      ((ρ : ℂ) • (R * pderiv 1 B) = (ω : ℂ) • (B * pderiv 1 R)) := by
  dsimp
  have hB : (leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])).IsWeightedHomogeneous
      (wt ρ (-(s : ℤ))) ω := by
    simpa only [leadingForm, hQweight] using
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := wt ρ (-(s : ℤ))) (ω : ℤ)
        (symbol (Q : Module.End ℂ ℂ[X])))
  have hbr := purePower_mate_poisson_base_eq_zero P Q R μ p ρ s ω
    hμ hp hsρ hω hR hexact hPweight hQweight hPface
  simpa only [Int.cast_natCast] using
    (homogeneous_poisson_derivative_identities
      (leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])) R
      ρ (-(s : ℤ)) ω ρ hB hRhom hbr)

/-- The derivative identities for the paper's concrete crossing face, with
homogeneity and nonvanishing of its base now proved rather than assumed. -/
theorem crossingFace_mate_derivative_identities
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
    ((ρ : ℂ) • (R * pderiv 0 B) = (ω : ℂ) • (B * pderiv 0 R)) ∧
      ((ρ : ℂ) • (R * pderiv 1 B) = (ω : ℂ) • (B * pderiv 1 R)) := by
  dsimp
  exact purePower_mate_derivative_identities P Q
    (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q) μ p ρ s ω
    hμ hp hsρ hω (crossingBase_ne_zero α q ρ s (Nat.zero_lt_of_lt hsρ))
    (crossingBase_isWeightedHomogeneous α q ρ s)
    hexact hPweight hQweight hPface

end Dixmier.Weyl
