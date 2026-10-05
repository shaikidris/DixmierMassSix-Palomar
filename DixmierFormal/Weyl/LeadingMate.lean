/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.LeadingPowers

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Leading-face compatibility of an exact Weyl pair

The exact relation `[Q,P]=1` forces the leading Poisson bracket to vanish
whenever its predicted weight is positive. This is the first step of the
paper's Euler and factor-order argument for the pure-power mate face.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

theorem symbol_one_A1 :
    symbol ((1 : A1 K) : Module.End K K[X]) = (1 : MvPolynomial (Fin 2) K) := by
  simpa [expo] using (symbol_concreteNormalMonomial (K := K) 0 0)

theorem vDeg_one_A1 (ρ σ : ℤ) :
    vDeg ρ σ ((1 : A1 K) : Module.End K K[X]) = 0 := by
  change WithBot.unbotD 0
    (weightedTotalDegree' (wt ρ σ)
      (symbol ((1 : A1 K) : Module.End K K[X]))) = 0
  rw [symbol_one_A1]
  simp [weightedTotalDegree', Finsupp.weight]

/-- The positive predicted commutator weight cannot occur, since an exact
Weyl commutator has weight zero. -/
theorem leadingPoisson_eq_zero_of_exact_commutator
    (P Q : A1 K) (ρ σ : ℤ) (hweight : 0 < ρ + σ)
    (hexact : Q * P - P * Q = 1)
    (htarget : 0 < vDeg ρ σ (Q : Module.End K K[X]) +
      vDeg ρ σ (P : Module.End K K[X]) - (ρ + σ)) :
    poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) = 0 := by
  by_contra hnonzero
  have hdeg := (leadingForm_commutator P Q ρ σ hweight hnonzero).1
  rw [hexact, vDeg_one_A1] at hdeg
  omega

/-- For an exact Weyl pair and a positive-sum Newton direction, the leading
Poisson bracket is either zero or one. If it is nonzero, the exact leading
commutator formula identifies it with the leading form of the constant one. -/
theorem exactPair_leadingPoisson_zero_or_one
    (P Q : A1 K) (ρ σ : ℤ) (hweight : 0 < ρ + σ)
    (hexact : Q * P - P * Q = 1) :
    poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) = 0 ∨
    poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) = 1 := by
  by_cases hzero : poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) = 0
  · exact Or.inl hzero
  · right
    have hlead := leadingForm_commutator P Q ρ σ hweight hzero
    rw [hexact, vDeg_one_A1] at hlead
    have hconst : leadingForm ρ σ ((1 : A1 K) : Module.End K K[X]) = 1 := by
      change MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ ((1 : A1 K) : Module.End K K[X]))
        (symbol ((1 : A1 K) : Module.End K K[X])) = 1
      rw [vDeg_one_A1, symbol_one_A1]
      apply MvPolynomial.ext
      intro d
      rw [MvPolynomial.coeff_weightedHomogeneousComponent]
      by_cases hd : d = 0
      · subst d
        simp
      · have h0d : 0 ≠ d := fun h => hd h.symm
        simp [MvPolynomial.coeff_one, h0d]
    rw [hconst] at hlead
    exact hlead.2.symm

/-- If the leading Poisson bracket is one, its predicted commutator weight
must be zero because the exact commutator is the constant operator one. -/
theorem exactPair_target_eq_zero_of_leadingPoisson_eq_one
    (P Q : A1 K) (ρ σ : ℤ) (hweight : 0 < ρ + σ)
    (hexact : Q * P - P * Q = 1)
    (hbracket : poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) = 1) :
    vDeg ρ σ (Q : Module.End K K[X]) + vDeg ρ σ (P : Module.End K K[X]) -
      (ρ + σ) = 0 := by
  have hlead := leadingForm_commutator P Q ρ σ hweight (by
    intro hzero
    rw [hzero] at hbracket
    norm_num at hbracket)
  rw [hexact, vDeg_one_A1] at hlead
  exact hlead.1.symm

/-- In the pure-power crossing setup, `v(P)=pρ`, `v(Q)=ω>0`, `p≥2`, and
`ρ>s` make the predicted commutator weight positive. Hence the leading
symbols Poisson-commute. This is the precise first step of Theorem 1.3. -/
theorem purePower_leadingPoisson_eq_zero
    (P Q : A1 ℂ) (p ρ s ω : ℕ) (hp : 2 ≤ p) (hsρ : s < ρ) (hω : 0 < ω)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω) :
    poisson (leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]))
      (leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X])) = 0 := by
  have hρz : 0 < (ρ : ℤ) := by exact_mod_cast (Nat.zero_lt_of_lt hsρ)
  have hsρz : (s : ℤ) < ρ := by exact_mod_cast hsρ
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hωz : 0 < (ω : ℤ) := by exact_mod_cast hω
  have hweight : 0 < (ρ : ℤ) + (-(s : ℤ)) := by omega
  have htarget : 0 < vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) +
      vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) -
        ((ρ : ℤ) + (-(s : ℤ))) := by
    rw [hPweight, hQweight]
    nlinarith [mul_nonneg (show 0 ≤ (p : ℤ) - 1 by omega) (le_of_lt hρz)]
  exact leadingPoisson_eq_zero_of_exact_commutator P Q ρ (-(s : ℤ))
    hweight hexact htarget

omit [CharZero K] in
/-- Differentiating a pure-power face factors its Poisson bracket by the
expected scalar and power of its primitive base. -/
theorem poisson_purePower_right (B R : MvPolynomial (Fin 2) K) (μ : K) (p : ℕ) :
    poisson B (MvPolynomial.C μ * R ^ p) =
      MvPolynomial.C μ * (p : MvPolynomial (Fin 2) K) * R ^ (p - 1) * poisson B R := by
  simp only [poisson, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow]
  ring

/-- In characteristic zero, a nonzero pure-power factor cannot hide a
nonzero Poisson bracket with its base. -/
theorem poisson_base_eq_zero_of_purePower
    (B R : MvPolynomial (Fin 2) K) (μ : K) (p : ℕ)
    (hμ : μ ≠ 0) (hp : 0 < p) (hR : R ≠ 0)
    (h : poisson B (MvPolynomial.C μ * R ^ p) = 0) :
    poisson B R = 0 := by
  rw [poisson_purePower_right] at h
  have hμpoly : (MvPolynomial.C μ : MvPolynomial (Fin 2) K) ≠ 0 := by
    simpa using hμ
  have hppoly : (p : MvPolynomial (Fin 2) K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hRpow : R ^ (p - 1) ≠ 0 := pow_ne_zero _ hR
  by_contra hbase
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hμpoly hppoly) hRpow) hbase) h

/-- Exact Weyl compatibility for a pure-power leading face: the mate's
leading symbol Poisson-commutes with the base `R`, before any factor-order
classification of that symbol. -/
theorem purePower_mate_poisson_base_eq_zero
    (P Q : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (μ : ℂ) (p ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hsρ : s < ρ) (hω : 0 < ω) (hR : R ≠ 0)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ * R ^ p) :
    poisson (leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])) R = 0 := by
  have hpoisson := purePower_leadingPoisson_eq_zero P Q p ρ s ω hp hsρ hω
    hexact hPweight hQweight
  rw [hPface] at hpoisson
  exact poisson_base_eq_zero_of_purePower _ R μ p hμ (by omega) hR hpoisson

end Dixmier.Weyl
