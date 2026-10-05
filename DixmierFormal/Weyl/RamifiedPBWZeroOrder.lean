/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedPBWRightShift

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First contraction when one ramified endpoint has order zero

This extends the PBW monomial endpoint coefficient to an order-zero
coefficient operator. It is required because Newton face endpoints may
lie on the horizontal axis.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWRightShift_single_zero_below
    (f : LaurentPolynomial ℂ) (n j : ℕ) (hjn : j < n) :
    ramifiedPBWRightShift (Finsupp.single 0 f) n j = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨a, ha⟩
  simp only [addRightEmbedding_apply] at ha
  omega

theorem ramifiedPBWCoeffs_coeffAtom_zero_below (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) (n j : ℕ) (hjn : j < n) :
    ramifiedPBWCoeffs l hl
      (ramifiedCoeffGen l f * (ramifiedYGen l)^n) j = 0 := by
  rw [ramifiedPBWCoeffs_rightShift,
    ramifiedPBWCoeffs_coeffGen]
  exact ramifiedPBWRightShift_single_zero_below f n j hjn

theorem ramifiedPBWCoeffs_positive_zero_product_next (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (j : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
        ramifiedCoeffGen l g) j =
      f * ((j+1 : ℂ) • ramifiedDerivative l g) := by
  have hshape :
      (ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
          ramifiedCoeffGen l g =
        ramifiedCoeffGen l f *
          ((ramifiedYGen l)^(j+1) * ramifiedCoeffGen l g) := by
    simp only [mul_assoc]
  rw [hshape, ramifiedPBWCoeffs_coeff_left,
    ramifiedCoeffLeftLinear_apply,
    ramifiedPBWCoeffs_derivativePow_next]

theorem ramifiedPBWCoeffs_zero_positive_product_next (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (j : ℕ) :
    ramifiedPBWCoeffs l hl
      (ramifiedCoeffGen l g *
        (ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1))) j = 0 := by
  rw [ramifiedPBWCoeffs_coeff_left,
    ramifiedCoeffLeftLinear_apply,
    ramifiedPBWCoeffs_coeffAtom_zero_below l hl f (j+1) j (by omega)]
  simp

/-- The first commutator coefficient for positive derivative order
against an order-zero Laurent coefficient operator. -/
theorem ramifiedPBWCoeffs_positive_zero_commutator_next (l : ℕ)
    (hl : 0 < l) (f g : LaurentPolynomial ℂ) (j : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
          ramifiedCoeffGen l g -
        ramifiedCoeffGen l g *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1))) j =
      f * ((j+1 : ℂ) • ramifiedDerivative l g) := by
  rw [ramifiedPBWCoeffs_sub, Finsupp.sub_apply,
    ramifiedPBWCoeffs_positive_zero_product_next,
    ramifiedPBWCoeffs_zero_positive_product_next]
  simp

theorem ramifiedPBWCoeffs_positive_zero_monomial_next (l : ℕ)
    (hl : 0 < l) (i u : ℤ) (j : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l (LaurentPolynomial.T i) *
          (ramifiedYGen l)^(j+1)) *
          ramifiedCoeffGen l (LaurentPolynomial.T u) -
        ramifiedCoeffGen l (LaurentPolynomial.T u) *
          (ramifiedCoeffGen l (LaurentPolynomial.T i) *
            (ramifiedYGen l)^(j+1))) j =
      (((j+1 : ℂ) * (u : ℂ)) / (l : ℂ)) •
        (LaurentPolynomial.T (i+u-(l : ℤ)) : LaurentPolynomial ℂ) := by
  rw [ramifiedPBWCoeffs_positive_zero_commutator_next,
    ramifiedDerivative_T]
  simp only [mul_smul_comm, ← LaurentPolynomial.T_add, smul_smul]
  have hi : i + (u - (l : ℤ)) = i + u - (l : ℤ) := by omega
  rw [hi]
  congr 1
  ring

theorem ramifiedCoeffGen_commute (l : ℕ)
    (f g : LaurentPolynomial ℂ) :
    ramifiedCoeffGen l f * ramifiedCoeffGen l g -
      ramifiedCoeffGen l g * ramifiedCoeffGen l f = 0 := by
  apply Subtype.ext
  change ramifiedCoeffMul f * ramifiedCoeffMul g -
    ramifiedCoeffMul g * ramifiedCoeffMul f = 0
  rw [ramifiedCoeffMul_mul, ramifiedCoeffMul_mul, mul_comm]
  exact sub_self _

end Dixmier.Weyl
