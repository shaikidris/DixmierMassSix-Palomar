/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.BivariateRatio
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Lowest-power arithmetic for a mate face

The constant power ratio proved for a strict crossing has an `x`-adic
consequence: comparison of the lowest `x`-powers forces an integral mate
exponent. This file isolates the polynomial order calculation.
-/

namespace Dixmier.Weyl

open Polynomial

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

/-- The lowest exponent in a nonzero polynomial power scales by its exponent. -/
theorem natTrailingDegree_pow_of_ne_zero
    (f : K[X]) (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).natTrailingDegree = n * f.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero n hf) hf, ih]
      ring

omit [NoZeroDivisors K] in
/-- A polynomial with nonzero constant term does not change the lowest
exponent of a pure power of `X`. -/
theorem natTrailingDegree_X_pow_mul_of_coeff_zero_ne_zero
    (g : K[X]) (n : ℕ) (h0 : g.coeff 0 ≠ 0) :
    (Polynomial.X ^ n * g).natTrailingDegree = n := by
  have hg : g ≠ 0 := by
    intro hz
    exact h0 (by simp [hz])
  rw [mul_comm, Polynomial.natTrailingDegree_mul_X_pow hg n]
  have hgd : g.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (.inr h0)
  omega

/-- If a nonzero power of `f` is a nonzero scalar times a polynomial whose
lowest exponent is `ω`, then `ρ` divides `ω`. -/
theorem power_ratio_lowest_order_divides
    (f g : K[X]) (c : K) (ρ ω : ℕ)
    (hf : f ≠ 0) (hc : c ≠ 0)
    (hgdegree : g.natTrailingDegree = ω)
    (h : f ^ ρ = Polynomial.C c * g) :
    ρ ∣ ω := by
  have hg : g ≠ 0 := by
    intro hz
    have hpow : f ^ ρ = 0 := by simpa [hz] using h
    exact (pow_ne_zero ρ hf) hpow
  have hnat := congrArg Polynomial.natTrailingDegree h
  rw [natTrailingDegree_pow_of_ne_zero f hf ρ,
    Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr hc) hg,
    Polynomial.natTrailingDegree_C c, hgdegree] at hnat
  exact ⟨f.natTrailingDegree, by simpa using hnat.symm⟩

/-- The face power starts at exactly `x^ω` for `s > 0`. -/
theorem crossingBase_power_natTrailingDegree
    (α : ℂ) (q ρ s ω : ℕ) (hs : 0 < s) :
    (((MvPolynomial.finSuccEquiv ℂ 1)
      ((MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω))).natTrailingDegree = ω := by
  let H : Polynomial (MvPolynomial (Fin 1) ℂ) :=
    (1 + Polynomial.C (MvPolynomial.C α) * Polynomial.X ^ s *
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) ^ ρ) ^ (q * ω)
  have h0 : H.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [H, hs.ne']
  have hX1 : MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ℂ) (n := 1) (j := 0))
  have hform :
      (MvPolynomial.finSuccEquiv ℂ 1)
        ((MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ ω) = Polynomial.X ^ ω * H := by
    simp only [map_pow, map_mul, map_add, map_one,
      MvPolynomial.finSuccEquiv_X_zero, hX1]
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    rw [mul_pow, ← pow_mul]
    rfl
  rw [hform]
  exact natTrailingDegree_X_pow_mul_of_coeff_zero_ne_zero H ω h0

/-- The constant power ratio on a strict crossing forces its mate weight to
be an integer multiple of the base weight. -/
theorem crossingBase_power_ratio_exponent_divides
    (B : MvPolynomial (Fin 2) ℂ) (α c : ℂ) (q ρ s ω : ℕ)
    (hs : 0 < s) (hB : B ≠ 0)
    (h : B ^ ρ = MvPolynomial.C c *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω) :
    ρ ∣ ω := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  have hEB : E B ≠ 0 := by
    intro hz
    exact hB (E.injective (by simpa using hz))
  have hc : c ≠ 0 := by
    intro hz
    have hbpow : B ^ ρ = 0 := by simpa [hz] using h
    exact (pow_ne_zero ρ hB) hbpow
  have hcC : (MvPolynomial.C c : MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    simpa using hc
  have hmap := congrArg E h
  have hmap' : (E B) ^ ρ = Polynomial.C (MvPolynomial.C c) *
      E ((MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω) := by
    simpa [E, MvPolynomial.finSuccEquiv_apply] using hmap
  exact power_ratio_lowest_order_divides (E B)
    (E ((MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
        MvPolynomial.X 1 ^ ρ) ^ q) ^ ω))
    (MvPolynomial.C c) ρ ω hEB hcC
    (crossingBase_power_natTrailingDegree α q ρ s ω hs) hmap'

/-- The actual strict-crossing Weyl mate has weight divisible by the base
weight. This is the first factor-order consequence in the paper's proof. -/
theorem crossingFace_mate_exponent_divides
    (P Q : A1 ℂ) (μ α : ℂ) (p q ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hs : 0 < s) (hsρ : s < ρ) (hω : 0 < ω)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ p) :
    ρ ∣ ω := by
  let B := leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])
  have hpos : 0 < vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) := by
    rw [hQweight]
    exact_mod_cast hω
  have hB : B ≠ 0 := leadingForm_ne_zero_of_vDeg_pos Q ρ (-(s : ℤ)) hpos
  obtain ⟨c, hc⟩ := crossingFace_mate_power_ratio_constant
    P Q μ α p q ρ s ω hμ hp hs hsρ hω hexact hPweight hQweight hPface
  exact crossingBase_power_ratio_exponent_divides B α c q ρ s ω hs hB hc

/-- Equality of nonzero positive powers gives equality of their logarithmic
derivatives after clearing denominators. -/
theorem cross_derivative_of_equal_powers
    (F G : MvPolynomial (Fin 2) ℂ) (c : ℂ) (n : ℕ)
    (hn : 0 < n) (hF : F ≠ 0)
    (h : F ^ n = MvPolynomial.C c * G ^ n)
    (i : Fin 2) :
    G * MvPolynomial.pderiv i F = F * MvPolynomial.pderiv i G := by
  have hd := congrArg (MvPolynomial.pderiv i) h
  simp only [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C_mul] at hd
  have hscalar : (n : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hpow : F ^ (n - 1) ≠ 0 := pow_ne_zero _ hF
  have hFpow : F * F ^ (n - 1) = F ^ n := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hGpow : G * G ^ (n - 1) = G ^ n := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hfactor : (n : MvPolynomial (Fin 2) ℂ) * F ^ (n - 1) *
      (G * MvPolynomial.pderiv i F - F * MvPolynomial.pderiv i G) = 0 := by
    calc
      _ = G * ((n : MvPolynomial (Fin 2) ℂ) * F ^ (n - 1) *
            MvPolynomial.pderiv i F) -
            (n : MvPolynomial (Fin 2) ℂ) *
              (F * F ^ (n - 1)) * MvPolynomial.pderiv i G := by ring
      _ = G * (MvPolynomial.C c * ((n : MvPolynomial (Fin 2) ℂ) *
            G ^ (n - 1) * MvPolynomial.pderiv i G)) -
            (n : MvPolynomial (Fin 2) ℂ) * F ^ n *
              MvPolynomial.pderiv i G := by rw [hd, hFpow]
      _ = (MvPolynomial.C c * (n : MvPolynomial (Fin 2) ℂ)) *
            (G * G ^ (n - 1)) * MvPolynomial.pderiv i G -
            (n : MvPolynomial (Fin 2) ℂ) * F ^ n *
              MvPolynomial.pderiv i G := by ring
      _ = 0 := by rw [hGpow, h]; ring
  have hprod : (n : MvPolynomial (Fin 2) ℂ) * F ^ (n - 1) ≠ 0 :=
    mul_ne_zero hscalar hpow
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hprod)

/-- The constant power-ratio identity yields the integer-power mate form on
a strict crossing face. The integer exponent is positive when `ω > 0`. -/
theorem crossingBase_power_ratio_mate_power
    (B : MvPolynomial (Fin 2) ℂ) (α c : ℂ) (q ρ s ω : ℕ)
    (hs : 0 < s) (hρ : 0 < ρ) (hω : 0 < ω) (hB : B ≠ 0)
    (h : B ^ ρ = MvPolynomial.C c *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω) :
    ∃ (j : ℕ) (ν : ℂ), 0 < j ∧ ω = ρ * j ∧
      B = MvPolynomial.C ν *
        (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ j := by
  let R : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
        MvPolynomial.X 1 ^ ρ) ^ q
  obtain ⟨j, hj⟩ := crossingBase_power_ratio_exponent_divides
    B α c q ρ s ω hs hB h
  have hjpos : 0 < j := by
    by_contra hj0
    have hz : j = 0 := Nat.eq_zero_of_not_pos hj0
    simp [hz] at hj
    omega
  have hpow : B ^ ρ = MvPolynomial.C c * (R ^ j) ^ ρ := by
    change B ^ ρ = MvPolynomial.C c * R ^ ω at h
    rw [hj, mul_comm ρ j, pow_mul] at h
    exact h
  have hx := cross_derivative_of_equal_powers B (R ^ j) c ρ hρ hB hpow 0
  have hy := cross_derivative_of_equal_powers B (R ^ j) c ρ hρ hB hpow 1
  obtain ⟨ν, hν⟩ := crossingBase_power_cross_derivatives_constant
    B α q ρ s j hs hx hy
  exact ⟨j, ν, hjpos, hj, hν⟩

/-- The genuine Weyl mate's strict-crossing leading face is a positive
integer power of the primitive base, with nonzero complex scalar. No bound on
the mate's degree, order, or mass is imposed. -/
theorem crossingFace_mate_is_base_power
    (P Q : A1 ℂ) (μ α : ℂ) (p q ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hs : 0 < s) (hsρ : s < ρ) (hω : 0 < ω)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ p) :
    ∃ (j : ℕ) (ν : ℂ), 0 < j ∧ ν ≠ 0 ∧ ω = ρ * j ∧
      leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) =
        MvPolynomial.C ν *
          (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ j := by
  let B := leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])
  have hpos : 0 < vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) := by
    rw [hQweight]
    exact_mod_cast hω
  have hB : B ≠ 0 := leadingForm_ne_zero_of_vDeg_pos Q ρ (-(s : ℤ)) hpos
  obtain ⟨c, hc⟩ := crossingFace_mate_power_ratio_constant
    P Q μ α p q ρ s ω hμ hp hs hsρ hω hexact hPweight hQweight hPface
  obtain ⟨j, ν, hjpos, hjweight, hν⟩ := crossingBase_power_ratio_mate_power
    B α c q ρ s ω hs (Nat.zero_lt_of_lt hsρ) hω hB hc
  have hνne : ν ≠ 0 := by
    intro hz
    apply hB
    simpa [hz] using hν
  exact ⟨j, ν, hjpos, hνne, hjweight, hν⟩

end Dixmier.Weyl
