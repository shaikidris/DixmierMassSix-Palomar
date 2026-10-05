/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
/-!
# Horizontal cross-derivative transport

After separating a horizontal face as `x^ω U(y)`, its exact second
cross-derivative equation becomes a one-variable Wronskian equation. The
existing polynomial Wronskian theorem then makes the ratio constant.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Transport a horizontal cross-derivative identity to the univariate
polynomial Wronskian of its coefficient factors. -/
theorem horizontal_cross_derivative_wronskian
    (U V : MvPolynomial (Fin 1) ℂ) (ω : ℕ)
    (hy :
      (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ V) *
          MvPolynomial.pderiv 1
            (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) =
      (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) *
          MvPolynomial.pderiv 1
            (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ V)) :
    Polynomial.wronskian
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) U)
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) V) = 0 := by
  have hdx : MvPolynomial.pderiv 1
      (MvPolynomial.X (0 : Fin 2) ^ ω : MvPolynomial (Fin 2) ℂ) = 0 := by
    simp
  simp only [MvPolynomial.pderiv_mul, hdx, zero_mul, zero_add,
    pderiv_one_rename_succ] at hy
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ≠ 0 := by simp
  have hsq : ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ ω) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (pow_ne_zero _ hx)
  have hrel : MvPolynomial.rename Fin.succ
      (V * MvPolynomial.pderiv 0 U - U * MvPolynomial.pderiv 0 V) = 0 := by
    have hmul : (MvPolynomial.X (0 : Fin 2) ^ ω) ^ 2 *
        MvPolynomial.rename Fin.succ
          (V * MvPolynomial.pderiv 0 U - U * MvPolynomial.pderiv 0 V) = 0 := by
      simp only [map_sub, map_mul]
      linear_combination hy
    exact (mul_eq_zero.mp hmul).resolve_left hsq
  have hsmall : V * MvPolynomial.pderiv 0 U - U * MvPolynomial.pderiv 0 V = 0 :=
    (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective 1))
      (by simpa using hrel)
  have hmap := congrArg (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)) hsmall
  simp only [map_sub, map_mul, map_zero, ← uniqueAlgEquiv_pderiv_zero] at hmap
  simp only [Polynomial.wronskian]
  linear_combination -hmap

/-- With a nonzero denominator coefficient, the horizontal Wronskian
identity forces scalar proportionality in the polynomial ring. -/
theorem horizontal_cross_derivative_scalar_ratio
    (U V : MvPolynomial (Fin 1) ℂ) (ω : ℕ) (hV : V ≠ 0)
    (hy :
      (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ V) *
          MvPolynomial.pderiv 1
            (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) =
      (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ U) *
          MvPolynomial.pderiv 1
            (MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ V)) :
    ∃ c : ℂ, U = MvPolynomial.C c * V := by
  let E := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  have hVE : E V ≠ 0 := E.map_ne_zero_iff.mpr hV
  have hw := horizontal_cross_derivative_wronskian U V ω hy
  obtain ⟨c, hc⟩ := polynomial_wronskian_zero_scalar_ratio (E U) (E V) hVE hw
  refine ⟨c, ?_⟩
  apply E.injective
  simpa [E, MvPolynomial.uniqueAlgEquiv_apply] using hc

end Dixmier.Weyl
