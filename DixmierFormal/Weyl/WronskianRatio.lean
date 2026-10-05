/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PowerRatio
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Algebra.Polynomial.FieldDivision

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Vanishing Wronskians and constant polynomial ratios

This file develops the one-variable algebraic kernel used when the bivariate
constant-ratio obligation is reduced along a polynomial variable.
-/

namespace Dixmier.Weyl

open Polynomial

variable {K : Type*} [Field K]

/-- A coprime complex polynomial pair with zero Wronskian differs by a scalar.
The general pair still requires removing its common gcd. -/
theorem coprime_wronskian_zero_scalar_ratio
    [CharZero K]
    (f g : K[X]) (hg : g ≠ 0) (hc : IsCoprime f g)
    (hw : Polynomial.wronskian f g = 0) :
    ∃ c : K, f = Polynomial.C c * g := by
  obtain ⟨hdf, hdg⟩ := hc.wronskian_eq_zero_iff.mp hw
  have hf : f = Polynomial.C (f.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hdf
  have hgc : g.coeff 0 ≠ 0 := by
    intro hzero
    apply hg
    simpa [hdg, hzero] using Polynomial.eq_C_of_derivative_eq_zero hdg
  refine ⟨f.coeff 0 / g.coeff 0, ?_⟩
  rw [hf, Polynomial.eq_C_of_derivative_eq_zero hdg]
  simp [← Polynomial.C_mul, hgc]

/-- A common polynomial factor contributes its square to the Wronskian. -/
theorem wronskian_common_mul (d f g : K[X]) :
    Polynomial.wronskian (d * f) (d * g) =
      d ^ 2 * Polynomial.wronskian f g := by
  simp only [Polynomial.wronskian, Polynomial.derivative_mul]
  ring

set_option linter.style.haveILetI false in
/-- Any two complex univariate polynomials with zero Wronskian and a nonzero
denominator differ by a scalar. This is the one-variable constant-ratio
theorem needed after a bivariate variable-separation step. -/
theorem polynomial_wronskian_zero_scalar_ratio
    [CharZero K]
    (f g : K[X]) (hg : g ≠ 0)
    (hw : Polynomial.wronskian f g = 0) :
    ∃ c : K, f = Polynomial.C c * g := by
  classical
  haveI : GCDMonoid K[X] := EuclideanDomain.gcdMonoid K[X]
  let d := GCDMonoid.gcd f g
  have hd : d ≠ 0 := gcd_ne_zero_of_right hg
  have hfd : d * (f / d) = f :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_left f g)
  have hgd : d * (g / d) = g :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_right f g)
  have hquot : Polynomial.wronskian (f / d) (g / d) = 0 := by
    have hfactor : d ^ 2 * Polynomial.wronskian (f / d) (g / d) = 0 := by
      rw [← wronskian_common_mul, hfd, hgd]
      exact hw
    exact (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero _ hd)
  obtain ⟨c, hc⟩ := coprime_wronskian_zero_scalar_ratio
    (f / d) (g / d) (right_div_gcd_ne_zero hg)
    (isCoprime_div_gcd_div_gcd hg) hquot
  refine ⟨c, ?_⟩
  calc
    f = d * (f / d) := hfd.symm
    _ = d * (Polynomial.C c * (g / d)) := by rw [hc]
    _ = Polynomial.C c * (d * (g / d)) := by ring
    _ = Polynomial.C c * g := by rw [hgd]

end Dixmier.Weyl
