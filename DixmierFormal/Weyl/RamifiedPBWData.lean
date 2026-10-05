/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedPBW

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical PBW coefficients, support, order, and weights

The positive-index ramified PBW uniqueness theorem supplies an actual
finitely supported coefficient sequence. Each coefficient is a Laurent
polynomial in `T=X^(1/l)`, so its two-dimensional support is finite.
Weight numerators are scaled by `l` to remain integral.

The leading support here is a finite support-level interface. G13's
ramified cut and its geometry remain to be formalized.
-/
namespace Dixmier.Weyl

/-- The canonical finitely supported sequence of Laurent coefficients. -/
noncomputable def ramifiedPBWCoeffs (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) : ℕ →₀ LaurentPolynomial ℂ :=
  Classical.choose (ramifiedOperatorAlgebra_unique_coefficients l hl
    (T : Module.End ℂ (LaurentPolynomial ℂ)) T.property)

theorem ramifiedPBWCoeffs_eval (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedNormalEval l (ramifiedPBWCoeffs l hl T) =
      (T : Module.End ℂ (LaurentPolynomial ℂ)) :=
  (Classical.choose_spec (ramifiedOperatorAlgebra_unique_coefficients l hl
    (T : Module.End ℂ (LaurentPolynomial ℂ)) T.property)).1

theorem ramifiedPBWCoeffs_eq_of_eval (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (a : ℕ →₀ LaurentPolynomial ℂ)
    (ha : ramifiedNormalEval l a =
      (T : Module.End ℂ (LaurentPolynomial ℂ))) :
    ramifiedPBWCoeffs l hl T = a :=
  (ramifiedNormalEval_injective l hl)
    ((ramifiedPBWCoeffs_eval l hl T).trans ha.symm)

/-- Maximum derivative exponent in the PBW expansion; zero for the
zero operator. -/
noncomputable def ramifiedPBWOrder (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) : ℕ :=
  (ramifiedPBWCoeffs l hl T).support.sup id

theorem ramifiedPBWCoeffs_eq_zero_of_order_lt (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : ramifiedPBWOrder l hl T < j) :
    (ramifiedPBWCoeffs l hl T) j = 0 := by
  by_contra hne
  have hmem : j ∈ (ramifiedPBWCoeffs l hl T).support :=
    Finsupp.mem_support_iff.mpr hne
  have hle : j ≤ ramifiedPBWOrder l hl T := by
    exact Finset.le_sup (f := id) hmem
  omega

/-- Coefficient of `T^i Y^j` in the canonical normal ordering. -/
noncomputable def ramifiedPBWCoeff (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (i : ℤ) (j : ℕ) : ℂ :=
  ((ramifiedPBWCoeffs l hl T) j).coeff i

/-- Finite support of the ramified PBW expansion. -/
noncomputable def ramifiedPBWSupport (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) : Finset (ℤ × ℕ) :=
  let a := ramifiedPBWCoeffs l hl T
  a.support.biUnion fun j => (a j).coeff.support.image fun i => (i,j)

theorem ramifiedPBWSupport_mem_iff (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (i : ℤ) (j : ℕ) :
    (i,j) ∈ ramifiedPBWSupport l hl T ↔
      ramifiedPBWCoeff l hl T i j ≠ 0 := by
  simp only [ramifiedPBWSupport, Finset.mem_biUnion, Finset.mem_image,
    ramifiedPBWCoeff]
  constructor
  · rintro ⟨k,hk,x,hx,hpair⟩
    have hi : x = i := (Prod.mk.inj hpair).1
    have hj : k = j := (Prod.mk.inj hpair).2
    subst x
    subst k
    exact Finsupp.mem_support_iff.mp hx
  · intro hc
    refine ⟨j, ?_, i, Finsupp.mem_support_iff.mpr hc, rfl⟩
    apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz] at hc

theorem ramifiedPBWSupport_order_bound (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T) :
    j ≤ ramifiedPBWOrder l hl T := by
  by_contra hbad
  have hz := ramifiedPBWCoeffs_eq_zero_of_order_lt l hl T j (by omega)
  have hnz := (ramifiedPBWSupport_mem_iff l hl T i j).mp hmem
  simp [ramifiedPBWCoeff, hz] at hnz

/-- The integral numerator of the `(ρ,σ)`-weight on `T^iY^j`,
where `T=X^(1/l)`. -/
def ramifiedWeight (l : ℕ) (ρ σ : ℤ) (p : ℤ × ℕ) : ℤ :=
  ρ * p.1 + (l : ℤ) * σ * p.2

/-- Maximum scaled weight, with junk value zero for empty support. -/
noncomputable def ramifiedWeightDeg (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (T : ramifiedOperatorAlgebra l) : ℤ :=
  WithBot.unbotD 0 ((ramifiedPBWSupport l hl T).sup fun p =>
    (ramifiedWeight l ρ σ p : WithBot ℤ))

/-- Support points attaining the maximum scaled weight. -/
noncomputable def ramifiedLeadingSupport (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (T : ramifiedOperatorAlgebra l) : Finset (ℤ × ℕ) :=
  (ramifiedPBWSupport l hl T).filter fun p =>
    ramifiedWeight l ρ σ p = ramifiedWeightDeg l hl ρ σ T

end Dixmier.Weyl
