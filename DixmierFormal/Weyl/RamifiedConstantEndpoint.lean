/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCanonicalFacePair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The constant-output boundary of the Newton endpoint criterion

For an exact commutator-one pair, a nonzero selected first-contraction
coefficient must be the constant PBW monomial. This is the boundary
used in G13 Proposition 2.4 and its application after the Newton cut.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_one_coeff_support
    (l : ℕ) (hl : 0 < l) (j : ℕ) (v : ℤ)
    (hv : v ∈ ((ramifiedPBWCoeffs l hl
      (1 : ramifiedOperatorAlgebra l)) j).coeff.support) :
    j = 0 ∧ v = 0 := by
  have hone : (1 : ramifiedOperatorAlgebra l) =
      ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one.symm
  rw [hone, ramifiedPBWCoeffs_coeffGen] at hv
  by_cases hj : j = 0
  · subst j
    simp only [Finsupp.single_eq_same] at hv
    have hsubset := AddMonoidAlgebra.support_coeff_one_subset
      (k := ℂ) (G := ℤ)
    have hv0 := hsubset hv
    simp at hv0
    exact ⟨rfl,hv0⟩
  · have hz : (Finsupp.single 0 (1 : LaurentPolynomial ℂ)) j = 0 :=
      Finsupp.single_eq_of_ne hj
    rw [hz] at hv
    simp at hv

theorem ramifiedPBWCoeffs_one_coeff_at_origin
    (l : ℕ) (hl : 0 < l) :
    ((ramifiedPBWCoeffs l hl
      (1 : ramifiedOperatorAlgebra l)) 0).coeff 0 = 1 := by
  have hone : (1 : ramifiedOperatorAlgebra l) =
      ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one.symm
  rw [hone, ramifiedPBWCoeffs_coeffGen]
  simp

theorem ramified_exact_pair_coeff_nonzero_iff_origin
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : P*Q-Q*P = 1) (j : ℕ) (v : ℤ) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v ≠ 0 ↔
      j = 0 ∧ v = 0 := by
  constructor
  · intro hne
    have hs : v ∈ ((ramifiedPBWCoeffs l hl
        (1 : ramifiedOperatorAlgebra l)) j).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa [hcomm] using hne
    exact ramifiedPBWCoeffs_one_coeff_support l hl j v hs
  · rintro ⟨rfl,rfl⟩
    rw [hcomm, ramifiedPBWCoeffs_one_coeff_at_origin]
    exact one_ne_zero

/-- The exact commutator turns any verified single-pair endpoint
coefficient formula into a two-way constant-endpoint criterion. -/
theorem ramified_exact_pair_determinant_nonzero_iff_origin
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : P*Q-Q*P = 1)
    (j : ℕ) (v : ℤ) (d a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcoeff : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      d*a*b) :
    d ≠ 0 ↔ j = 0 ∧ v = 0 := by
  have horigin := ramified_exact_pair_coeff_nonzero_iff_origin
    l hl P Q hcomm j v
  constructor
  · intro hd
    apply horigin.mp
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero hd ha) hb
  · intro hpoint
    have hnz := horigin.mpr hpoint
    rw [hcoeff] at hnz
    intro hd
    simp [hd] at hnz

end Dixmier.Weyl
