/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Power cancellation in the homogeneous-companion argument

This is the algebraic last step of GGV Proposition 2.6.  It does not provide
the proper-power leading form or the preliminary homogeneous companion.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem poisson_power_left (R F : MvPolynomial (Fin 2) ℂ) (k : ℕ) :
    poisson (R ^ k) F = (k : MvPolynomial (Fin 2) ℂ) * R ^ (k - 1) * poisson R F := by
  simp only [poisson, MvPolynomial.pderiv_pow]
  ring

theorem poisson_power_companion_cancel
    (R F : MvPolynomial (Fin 2) ℂ) (μ : ℂ) (k : ℕ)
    (hμ : μ ≠ 0) (hk : 0 < k) (hR : R ≠ 0)
    (h : poisson (C μ * R ^ k) F = C μ * R ^ k) :
    poisson R (C (k : ℂ) * F) = R := by
  have hμp : (C μ : MvPolynomial (Fin 2) ℂ) ≠ 0 := by simpa using hμ
  have hkp : (k : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hpow : R ^ (k - 1) ≠ 0 := pow_ne_zero _ hR
  have hpowk : R ^ k = R ^ (k - 1) * R := by
    rw [← pow_succ]
    congr 1
    omega
  have hfactor : (C μ * R ^ (k - 1)) *
      ((k : MvPolynomial (Fin 2) ℂ) * poisson R F) =
      (C μ * R ^ (k - 1)) * R := by
    have hleft : poisson (C μ * R ^ k) F = C μ * poisson (R ^ k) F := by
      simp only [poisson, MvPolynomial.pderiv_C_mul]
      ring
    rw [hleft, poisson_power_left, hpowk] at h
    calc
      _ = C μ * ((k : MvPolynomial (Fin 2) ℂ) * R ^ (k - 1) * poisson R F) := by ring
      _ = C μ * (R ^ (k - 1) * R) := h
      _ = _ := by ring
  have hc : (k : MvPolynomial (Fin 2) ℂ) * poisson R F = R := by
    exact mul_left_cancel₀ (mul_ne_zero hμp hpow) hfactor
  calc
    poisson R (C (k : ℂ) * F) =
        (k : MvPolynomial (Fin 2) ℂ) * poisson R F := by
          change poisson R (C (k : ℂ) * F) = C (k : ℂ) * poisson R F
          simp only [poisson, MvPolynomial.pderiv_C_mul]
          ring
    _ = R := hc

end Dixmier.Weyl
