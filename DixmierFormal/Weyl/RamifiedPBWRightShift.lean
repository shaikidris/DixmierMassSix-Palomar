/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstContraction

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Right multiplication by a ramified derivative power

In normal ordering, right multiplication by `Y^k` only shifts the
derivative index by `k`. This is needed to turn the first-contraction
formula into a two-operator commutator coefficient.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedPBWRightShift (a : ℕ →₀ LaurentPolynomial ℂ)
    (k : ℕ) : ℕ →₀ LaurentPolynomial ℂ :=
  Finsupp.embDomain (addRightEmbedding k) a

@[simp] theorem ramifiedPBWRightShift_apply (a : ℕ →₀ LaurentPolynomial ℂ)
    (k j : ℕ) : ramifiedPBWRightShift a k (j+k) = a j := by
  exact Finsupp.embDomain_apply_self (addRightEmbedding k) a j

theorem ramifiedNormalEval_rightShift (l : ℕ)
    (a : ℕ →₀ LaurentPolynomial ℂ) (k : ℕ) :
    ramifiedNormalEval l (ramifiedPBWRightShift a k) =
      ramifiedNormalEval l a * (ramifiedDerivative l)^k := by
  induction a using Finsupp.induction_linear with
  | zero => simp [ramifiedPBWRightShift, ramifiedNormalEval]
  | add a b ha hb =>
      rw [ramifiedPBWRightShift, Finsupp.embDomain_add,
        ← ramifiedNormalEvalLinear_apply, map_add,
        ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_apply]
      have hsum : ramifiedNormalEval l (a+b) =
          ramifiedNormalEval l a + ramifiedNormalEval l b := by
        rw [← ramifiedNormalEvalLinear_apply, map_add,
          ramifiedNormalEvalLinear_apply, ramifiedNormalEvalLinear_apply]
      rw [hsum, add_mul]
      exact congrArg₂ (· + ·) ha hb
  | single j f =>
      rw [ramifiedPBWRightShift, Finsupp.embDomain_single]
      rw [← ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_single,
        ← ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_single]
      simp only [addRightEmbedding_apply, mul_assoc, ← pow_add]

theorem ramifiedPBWCoeffs_rightShift (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (k : ℕ) :
    ramifiedPBWCoeffs l hl (T * (ramifiedYGen l)^k) =
      ramifiedPBWRightShift (ramifiedPBWCoeffs l hl T) k := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [ramifiedNormalEval_rightShift, ramifiedPBWCoeffs_eval]
  rfl

theorem ramifiedPBWCoeffs_atomProduct_next (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (j k : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)))
      (j+k+1) =
        f * ((j+1 : ℂ) • ramifiedDerivative l g) := by
  have hshape :
      (ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) =
        ramifiedCoeffGen l f *
          (((ramifiedYGen l)^(j+1) * ramifiedCoeffGen l g) *
            (ramifiedYGen l)^(k+1)) := by
    simp only [mul_assoc]
  rw [hshape, ramifiedPBWCoeffs_coeff_left,
    ramifiedPBWCoeffs_rightShift,
    ramifiedPBWCoeffs_derivativePow_coeff,
    ramifiedCoeffLeftLinear_apply]
  have hindex : j+k+1 = j+(k+1) := by omega
  rw [hindex, ramifiedPBWRightShift_apply,
    ramifiedDerivativePBWPower_next]

/-- Every derivative coefficient of a product of two PBW atoms is the
left Laurent coefficient times one coefficient of `Y^n g`. -/
theorem ramifiedPBWCoeffs_atomProduct_all (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m r : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) (r+m) =
      f * ramifiedDerivativePBWPower l g n r := by
  have hshape :
      (ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) =
        ramifiedCoeffGen l f *
          (((ramifiedYGen l)^n * ramifiedCoeffGen l g) *
            (ramifiedYGen l)^m) := by
    simp only [mul_assoc]
  rw [hshape, ramifiedPBWCoeffs_coeff_left,
    ramifiedPBWCoeffs_rightShift,
    ramifiedPBWCoeffs_derivativePow_coeff,
    ramifiedCoeffLeftLinear_apply,
    ramifiedPBWRightShift_apply]

theorem ramifiedPBWCoeffs_sub (l : ℕ) (hl : 0 < l)
    (T U : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (T-U) =
      ramifiedPBWCoeffs l hl T - ramifiedPBWCoeffs l hl U := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [ramifiedNormalEval_sub,
    ramifiedPBWCoeffs_eval, ramifiedPBWCoeffs_eval]
  rfl

/-- The zero-contraction coefficient of every PBW atom commutator
vanishes, including when an atom has derivative order zero. -/
theorem ramifiedPBWCoeffs_atomCommutator_top_zero (l : ℕ)
    (hl : 0 < l) (f g : LaurentPolynomial ℂ) (n m : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) (n+m) = 0 := by
  rw [ramifiedPBWCoeffs_sub, Finsupp.sub_apply,
    ramifiedPBWCoeffs_atomProduct_all l hl f g n m n,
    ramifiedDerivativePBWPower_top]
  have hindex : n+m = m+n := by omega
  rw [hindex, ramifiedPBWCoeffs_atomProduct_all l hl g f m n m,
    ramifiedDerivativePBWPower_top]
  exact sub_eq_zero.mpr (mul_comm f g)

/-- The coefficient one derivative order below the canceled top term
of an arbitrary pair of positive-order ramified PBW monomials. -/
theorem ramifiedPBWCoeffs_atomCommutator_next (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (j k : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^(j+1)))
      (j+k+1) =
        f * ((j+1 : ℂ) • ramifiedDerivative l g) -
          g * ((k+1 : ℂ) • ramifiedDerivative l f) := by
  rw [ramifiedPBWCoeffs_sub, Finsupp.sub_apply,
    ramifiedPBWCoeffs_atomProduct_next]
  have hindex : j+k+1 = k+j+1 := by omega
  rw [hindex, ramifiedPBWCoeffs_atomProduct_next]

/-- The first contraction of two ramified PBW monomials has the
determinant coefficient used in G13's endpoint criterion. -/
theorem ramifiedPBWCoeffs_monomialCommutator_next (l : ℕ) (hl : 0 < l)
    (i u : ℤ) (j k : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l (LaurentPolynomial.T i) *
          (ramifiedYGen l)^(j+1)) *
          (ramifiedCoeffGen l (LaurentPolynomial.T u) *
            (ramifiedYGen l)^(k+1)) -
        (ramifiedCoeffGen l (LaurentPolynomial.T u) *
          (ramifiedYGen l)^(k+1)) *
          (ramifiedCoeffGen l (LaurentPolynomial.T i) *
            (ramifiedYGen l)^(j+1)))
      (j+k+1) =
        (((j+1 : ℂ) * (u : ℂ) - (k+1 : ℂ) * (i : ℂ)) /
          (l : ℂ)) •
          (LaurentPolynomial.T (i+u-(l : ℤ)) : LaurentPolynomial ℂ) := by
  rw [ramifiedPBWCoeffs_atomCommutator_next,
    ramifiedDerivative_T, ramifiedDerivative_T]
  simp only [mul_smul_comm, ← LaurentPolynomial.T_add]
  have h₁ : i + (u - (l : ℤ)) = i + u - (l : ℤ) := by omega
  have h₂ : u + (i - (l : ℤ)) = i + u - (l : ℤ) := by omega
  rw [h₁, h₂]
  rw [smul_smul, smul_smul, ← sub_smul]
  congr 1
  ring

end Dixmier.Weyl
