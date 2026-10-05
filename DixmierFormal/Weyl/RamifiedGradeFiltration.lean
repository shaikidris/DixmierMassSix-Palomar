/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedGradeExactPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Filtration action of a ramified PBW grade bound

This extends the strict-negative upper-bound action to an arbitrary
integer grade bound. The nonpositive case preserves the upper-exponent
filtration and is the first half of an exact-pair zero-grade obstruction.
-/

namespace Dixmier.Weyl

theorem ramified_grade_bound_maps_upper
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (c : ℤ)
    (hbound : ∀ p ∈ ramifiedPBWSupport l hl T,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ c)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) :
    LaurentUpper ((T : Module.End ℂ (LaurentPolynomial ℂ)) f)
      (B + c) := by
  rw [← ramifiedPBWCoeffs_eval l hl T,
    ramifiedNormalEval_apply, Finsupp.sum]
  apply LaurentUpper_finset_sum
  intro j hj
  have hcoeff : LaurentUpper ((ramifiedPBWCoeffs l hl T) j)
      ((l : ℤ) * (j : ℤ) + c) := by
    intro i hi
    have hmem : (i,j) ∈ ramifiedPBWSupport l hl T :=
      (ramifiedPBWSupport_mem_iff l hl T i j).mpr
        (Finsupp.mem_support_iff.mp hi)
    have h := hbound (i,j) hmem
    dsimp at h
    omega
  have hder := LaurentUpper_derivative_pow l f B hf j
  have hmul := LaurentUpper_mul
    ((ramifiedPBWCoeffs l hl T) j)
    (((ramifiedDerivative l)^j) f)
    ((l : ℤ) * (j : ℤ) + c)
    (B - (l : ℤ) * (j : ℤ)) hcoeff hder
  convert hmul using 1
  omega

theorem ramified_nonpositive_grade_preserves_upper
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l)
    (hbound : ∀ p ∈ ramifiedPBWSupport l hl T,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ 0)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) :
    LaurentUpper ((T : Module.End ℂ (LaurentPolynomial ℂ)) f) B := by
  simpa using ramified_grade_bound_maps_upper l hl T 0 hbound f B hf

/-- In the upper-zero Laurent filtration, vanishing of the coefficient
at exponent zero is exactly the strict upper-bound condition needed below. -/
theorem LaurentUpper_zero_coeff_strict
    (f : LaurentPolynomial ℂ)
    (hf : LaurentUpper f 0) (hcoeff : f.coeff 0 = 0) :
    LaurentUpper f (-1) := by
  intro i hi
  have hle := hf i hi
  have hne : i ≠ 0 := by
    intro hz
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hcoeff
  omega

theorem LaurentUpper_smul_local
    (c : ℂ) (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) : LaurentUpper (c • f) B := by
  intro i hi
  have hnz : (c • f).coeff i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hfi : f.coeff i ≠ 0 := by
    intro hz
    simp [hz] at hnz
  exact hf i (Finsupp.mem_support_iff.mpr hfi)

/-- A nonpositive-grade ramified operator acts on the one-dimensional
top quotient of the upper-zero Laurent filtration: a vector whose top
coefficient vanishes remains top-zero after applying the operator. -/
theorem ramified_nonpositive_grade_preserves_zero_top_coeff
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l)
    (hbound : ∀ p ∈ ramifiedPBWSupport l hl T,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ 0)
    (f : LaurentPolynomial ℂ)
    (hf : LaurentUpper f 0) (hcoeff : f.coeff 0 = 0) :
    (((T : Module.End ℂ (LaurentPolynomial ℂ)) f).coeff 0) = 0 := by
  have hstrict := LaurentUpper_zero_coeff_strict f hf hcoeff
  have hout := ramified_nonpositive_grade_preserves_upper
    l hl T hbound f (-1) hstrict
  exact LaurentUpper_coeff_zero_above _ (-1) 0 hout (by omega)

/-- On upper-zero Laurent polynomials, a nonpositive-grade operator acts
by a scalar on the top coefficient. The scalar is its action on `1`. -/
theorem ramified_nonpositive_grade_top_coeff_action
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l)
    (hbound : ∀ p ∈ ramifiedPBWSupport l hl T,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ 0)
    (f : LaurentPolynomial ℂ) (hf : LaurentUpper f 0) :
    (((T : Module.End ℂ (LaurentPolynomial ℂ)) f).coeff 0) =
      f.coeff 0 *
        (((T : Module.End ℂ (LaurentPolynomial ℂ)) 1).coeff 0) := by
  let c : ℂ := f.coeff 0
  let g : LaurentPolynomial ℂ := f - c • 1
  have hupperG : LaurentUpper g 0 := by
    exact LaurentUpper_sub_local f (c • 1) 0 hf
      (LaurentUpper_smul_local c 1 0 LaurentUpper_one)
  have hcoeffG : g.coeff 0 = 0 := by
    simp [g, c, AddMonoidAlgebra.coeff_sub]
  have hzero := ramified_nonpositive_grade_preserves_zero_top_coeff
    l hl T hbound g hupperG hcoeffG
  dsimp [g] at hzero
  simp only [map_sub, map_smul, AddMonoidAlgebra.coeff_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- An exact ramified Weyl pair cannot have both supports entirely in
nonpositive diagonal grade. The upper-zero Laurent quotient is one
dimensional, so the two induced scalar actions commute. -/
theorem ramified_exact_pair_not_both_nonpositive_grade
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hP : ∀ p ∈ ramifiedPBWSupport l hl P,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ 0)
    (hQ : ∀ q ∈ ramifiedPBWSupport l hl Q,
      q.1 - (l : ℤ) * (q.2 : ℤ) ≤ 0) : False := by
  let one : LaurentPolynomial ℂ := 1
  have hPupper : LaurentUpper
      ((P : Module.End ℂ (LaurentPolynomial ℂ)) one) 0 :=
    ramified_nonpositive_grade_preserves_upper l hl P hP one 0 LaurentUpper_one
  have hQupper : LaurentUpper
      ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one) 0 :=
    ramified_nonpositive_grade_preserves_upper l hl Q hQ one 0 LaurentUpper_one
  have hQP := ramified_nonpositive_grade_top_coeff_action l hl Q hQ
    ((P : Module.End ℂ (LaurentPolynomial ℂ)) one) hPupper
  have hPQ := ramified_nonpositive_grade_top_coeff_action l hl P hP
    ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one) hQupper
  have hact := congrArg
    (fun U : ramifiedOperatorAlgebra l =>
      (U : Module.End ℂ (LaurentPolynomial ℂ)) one) hcomm
  change (Q : Module.End ℂ (LaurentPolynomial ℂ))
      ((P : Module.End ℂ (LaurentPolynomial ℂ)) one) -
      (P : Module.End ℂ (LaurentPolynomial ℂ))
        ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one) = one at hact
  have hcoeff := congrArg (fun f : LaurentPolynomial ℂ => f.coeff 0) hact
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hcoeff
  rw [hQP, hPQ] at hcoeff
  have hone : one.coeff 0 = 1 := by
    simp [one, ← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply]
  rw [hone] at hcoeff
  have hPone : ((P : Module.End ℂ (LaurentPolynomial ℂ)) 1).coeff 0 =
      ((P : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 := rfl
  have hQone : ((Q : Module.End ℂ (LaurentPolynomial ℂ)) 1).coeff 0 =
      ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 := rfl
  rw [hPone, hQone] at hcoeff
  have hzero : (0 : ℂ) = 1 := by
    calc
      _ = ((P : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 *
            ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 -
          ((Q : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 *
            ((P : Module.End ℂ (LaurentPolynomial ℂ)) one).coeff 0 := by ring
      _ = 1 := hcoeff
  norm_num at hzero

/-- Every exact ramified pair has an occupied positive-grade PBW point
in at least one member. This strengthens the earlier nonnegative support
conclusion, while making no claim about which member supplies it. -/
theorem ramified_exact_pair_has_positive_grade_point
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1) :
    (∃ p ∈ ramifiedPBWSupport l hl P,
      0 < p.1 - (l : ℤ) * (p.2 : ℤ)) ∨
    (∃ q ∈ ramifiedPBWSupport l hl Q,
      0 < q.1 - (l : ℤ) * (q.2 : ℤ)) := by
  by_contra hnone
  push Not at hnone
  have hP : ∀ p ∈ ramifiedPBWSupport l hl P,
      p.1 - (l : ℤ) * (p.2 : ℤ) ≤ 0 := by
    intro p hp
    exact hnone.1 p hp
  have hQ : ∀ q ∈ ramifiedPBWSupport l hl Q,
      q.1 - (l : ℤ) * (q.2 : ℤ) ≤ 0 := by
    intro q hq
    exact hnone.2 q hq
  exact ramified_exact_pair_not_both_nonpositive_grade
    l hl P Q hcomm hP hQ

end Dixmier.Weyl
