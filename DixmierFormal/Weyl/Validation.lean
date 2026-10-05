/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.LinearCombination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Validation of the Weyl-algebra definitions

Checks that the operator model has the paper's commutation convention `[Y, X] = 1`, that the
generators lie in `A1 K`, and that the coefficient-extraction formula recovers the PBW symbol
`x` of multiplication by `X` (so `mass xOp = 1`).
-/

namespace Dixmier.Weyl

open Polynomial Finset

variable {K : Type*} [Field K]

/-- `[Y, X] = 1` in `End_K(K[X])`. -/
theorem yOp_mul_xOp_sub_xOp_mul_yOp : yOp K * xOp K - xOp K * yOp K = 1 := by
  refine LinearMap.ext fun p => ?_
  simp [xOp, yOp, Module.End.mul_apply, derivative_mul]

private theorem xOp_pow_apply (i : ℕ) : ∀ p : K[X], (xOp K ^ i) p = X ^ i * p := by
  induction i with
  | zero => intro p; simp [xOp]
  | succ i ih =>
      intro p
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [xOp, LinearMap.mulLeft_apply, pow_succ, mul_assoc]

private theorem yOp_pow_apply (j : ℕ) (p : K[X]) :
    (yOp K ^ j) p = Polynomial.derivative^[j] p := by
  rw [Module.End.pow_apply]
  rfl

/-- Normal ordering for a power of the derivative followed by a power of multiplication by `X`.
The sum is the finite Leibniz expansion; its coefficients are the binomial coefficient times a
falling factorial. -/
theorem yOp_pow_mul_xOp_pow (i j : ℕ) :
    yOp K ^ j * xOp K ^ i =
      ∑ k ∈ Finset.range (min i j).succ,
        (j.choose k * i.descFactorial k : K) •
          (xOp K ^ (i - k) * yOp K ^ (j - k)) := by
  refine LinearMap.ext fun p => ?_
  calc
    (yOp K ^ j * xOp K ^ i) p = Polynomial.derivative^[j] (p * X ^ i) := by
      simp [Module.End.mul_apply, xOp_pow_apply, yOp_pow_apply, mul_comm]
    _ = _ := Polynomial.iterate_derivative_mul_X_pow j i p
    _ =
        (∑ k ∈ Finset.range (min i j).succ,
          (j.choose k * i.descFactorial k : K) •
            (xOp K ^ (i - k) * yOp K ^ (j - k))) p := by
      simp [Module.End.mul_apply, xOp_pow_apply, yOp_pow_apply, mul_comm,
        Polynomial.smul_eq_C_mul]


section PBWCoefficientInversion

private theorem binom_sub_pow (j : ℕ) :
    (X - C (1 : K) : K[X]) ^ j =
      ∑ k ∈ range (j + 1), C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ k := by
  rw [sub_eq_add_neg, add_pow]
  refine sum_congr rfl ?_
  intro k hk
  simp [mul_comm, mul_assoc, C_mul]

private theorem alternating_binomial_descFactorial (j b : ℕ) :
    ∑ k ∈ range (j + 1),
      ((-1 : K) ^ (j-k)) * (j.choose k : K) * (k.descFactorial b : K) =
      if j = b then j.factorial else 0 := by
  have hpoly := binom_sub_pow (K := K) j
  have h := congrArg (fun p : K[X] => p.eval 1) (congrArg (derivative^[b]) hpoly)
  have hsum :
      eval 1 (derivative^[b] (∑ k ∈ range (j + 1),
        C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ k)) =
      ∑ k ∈ range (j + 1),
        ((-1 : K) ^ (j-k)) * (j.choose k : K) * (k.descFactorial b : K) := by
    rw [iterate_derivative_sum]
    change (evalRingHom (1 : K)) (∑ k ∈ range (j + 1),
      derivative^[b] (C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ k)) = _
    rw [map_sum]
    refine sum_congr rfl ?_
    intro k hk
    rw [← Polynomial.smul_eq_C_mul, iterate_derivative_smul, iterate_derivative_X_pow_eq_smul]
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, map_mul, map_mul]
    simp [coe_evalRingHom, eval_X, eval_pow, mul_comm, mul_left_comm]
  have hleft : eval 1 (derivative^[b] ((X - C (1 : K) : K[X]) ^ j)) =
      if j = b then (j.factorial : K) else 0 := by
    rw [iterate_derivative_X_sub_pow, ← Nat.cast_smul_eq_nsmul K, Polynomial.smul_eq_C_mul, eval_mul, eval_C]
    by_cases hj : j = b
    · subst b
      simp [Nat.descFactorial_self]
    · by_cases hbj : b ≤ j
      · have hbj' : b < j := lt_of_le_of_ne hbj (Ne.symm hj)
        have hpos : 0 < j-b := Nat.sub_pos_of_lt hbj'
        simp [eval_sub, eval_X, hj, Nat.ne_of_gt hpos]
      · have hjb : j < b := Nat.lt_of_not_ge hbj
        simp [Nat.descFactorial_eq_zero_iff_lt.mpr hjb, hj]
  calc
    _ = eval 1 (derivative^[b] (∑ k ∈ range (j + 1),
          C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ k)) := hsum.symm
    _ = eval 1 (derivative^[b] ((X - C (1 : K) : K[X]) ^ j)) := h.symm
    _ = _ := by simpa using hleft

private theorem normalOrdered_monomial_apply (a b k : ℕ) :
    ((xOp K ^ a * yOp K ^ b) (X ^ k : K[X])) =
      X ^ a * (C (k.descFactorial b : K) * X ^ (k-b)) := by
  simp [Module.End.mul_apply, xOp_pow_apply, yOp_pow_apply,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]

variable [CharZero K]

private theorem normalOrdered_coefficient_term (a b j k : ℕ) (hk : k ∈ range (j+1)) :
    C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ (j-k) *
      ((xOp K ^ a * yOp K ^ b) (X ^ k : K[X])) =
    C (((-1 : K) ^ (j-k)) * (j.choose k : K) * (k.descFactorial b : K)) *
      X ^ (a + j-b) := by
  rw [normalOrdered_monomial_apply]
  by_cases hbk : b ≤ k
  · have hk' : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hex : (j-k) + a + (k-b) = a + j-b := by omega
    calc
      _ = (C (((-1 : K) ^ (j-k)) * (j.choose k : K)) *
          C (k.descFactorial b : K)) * X ^ ((j-k)+a+(k-b)) := by ring
      _ = _ := by rw [hex, ← C_mul]
  · have hkb : k < b := Nat.lt_of_not_ge hbk
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkb]

private theorem coeffPoly_normalOrdered_monomial (a b j : ℕ) :
    coeffPoly (xOp K ^ a * yOp K ^ b) j = if j = b then X ^ a else 0 := by
  by_cases hbj : b ≤ j
  · have hsum :
      (∑ k ∈ range (j+1), C (((-1 : K) ^ (j-k)) * (j.choose k : K)) * X ^ (j-k) *
        ((xOp K ^ a * yOp K ^ b) (X ^ k : K[X]))) =
      (∑ k ∈ range (j+1), C (((-1 : K) ^ (j-k)) * (j.choose k : K) *
        (k.descFactorial b : K))) * X ^ (a+j-b) := by
      calc
        _ = ∑ k ∈ range (j+1), C (((-1 : K) ^ (j-k)) * (j.choose k : K) *
            (k.descFactorial b : K)) * X ^ (a+j-b) := by
          refine sum_congr rfl ?_
          intro k hk
          exact normalOrdered_coefficient_term a b j k hk
        _ = _ := by rw [Finset.sum_mul]
    have hcast :
      (∑ k ∈ range (j+1), C (((-1 : K) ^ (j-k)) * (j.choose k : K) *
        (k.descFactorial b : K))) =
      C (∑ k ∈ range (j+1), ((-1 : K) ^ (j-k)) * (j.choose k : K) *
        (k.descFactorial b : K)) := by
      rw [← map_sum]
    rw [coeffPoly, hsum, hcast, alternating_binomial_descFactorial]
    by_cases hjb : j = b
    · subst b
      have hfac : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      simp
      change C ((j.factorial : K)⁻¹) * (C (j.factorial : K) * X ^ a) = X ^ a
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hfac]
      simp
    · have hlt : b < j := lt_of_le_of_ne hbj (Ne.symm hjb)
      simp [hjb]
  · have hjb : j < b := Nat.lt_of_not_ge hbj
    rw [coeffPoly]
    have hz : ∀ k ∈ range (j+1),
      ((xOp K ^ a * yOp K ^ b) (X ^ k : K[X])) = 0 := by
      intro k hk
      have hk' : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hkb : k < b := lt_of_le_of_lt hk' hjb
      rw [normalOrdered_monomial_apply]
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkb]
    have hzero :
        (∑ k ∈ range (j+1), C (((-1 : K) ^ (j-k)) * (j.choose k : K)) *
          X ^ (j-k) * ((xOp K ^ a * yOp K ^ b) (X ^ k : K[X]))) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [hz k hk]
      simp
    rw [hzero]
    have hneq : j ≠ b := Nat.ne_of_lt hjb
    simp [hneq]

/-- The coefficient extractor returns one on the matching normal-ordered PBW monomial and zero
on every other monomial. The characteristic-zero assumption is needed because `coeffPoly` uses
the inverse of `j!`. -/
theorem pbwCoeff_normalOrdered_monomial (a b i j : ℕ) :
    pbwCoeff (xOp K ^ a * yOp K ^ b) i j = if i = a ∧ j = b then 1 else 0 := by
  unfold pbwCoeff
  rw [coeffPoly_normalOrdered_monomial]
  by_cases hj : j = b
  · subst j
    simp [coeff_X_pow]
  · simp [hj]

omit [CharZero K] in
private theorem coeffPoly_add (T U : Module.End K K[X]) (j : ℕ) :
    coeffPoly (T + U) j = coeffPoly T j + coeffPoly U j := by
  unfold coeffPoly
  simp_rw [LinearMap.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

omit [CharZero K] in
theorem pbwCoeff_add (T U : Module.End K K[X]) (i j : ℕ) :
    pbwCoeff (T + U) i j = pbwCoeff T i j + pbwCoeff U i j := by
  simp [pbwCoeff, coeffPoly_add]

omit [CharZero K] in
private theorem coeffPoly_smul (c : K) (T : Module.End K K[X]) (j : ℕ) :
    coeffPoly (c • T) j = c • coeffPoly T j := by
  unfold coeffPoly
  simp_rw [LinearMap.smul_apply]
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum, mul_smul_comm]

omit [CharZero K] in
theorem pbwCoeff_smul (c : K) (T : Module.End K K[X]) (i j : ℕ) :
    pbwCoeff (c • T) i j = c * pbwCoeff T i j := by
  simp [pbwCoeff, coeffPoly_smul, Polynomial.coeff_smul]


theorem pbwCoeff_finiteNormalOrderedSum (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → K) (i j : ℕ) :
    pbwCoeff (∑ p ∈ s, c p • (xOp K ^ p.1 * yOp K ^ p.2)) i j =
      ∑ p ∈ s, if i = p.1 ∧ j = p.2 then c p else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pbwCoeff, coeffPoly]
  | insert p s hnot ih =>
      simp only [Finset.sum_insert hnot]
      rw [pbwCoeff_add, pbwCoeff_smul,
        pbwCoeff_normalOrdered_monomial]
      simp [ih]

theorem pbwCoeff_finiteNormalOrderedSum_recovery
    (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → K) (i j : ℕ) :
    pbwCoeff (∑ p ∈ s, c p • (xOp K ^ p.1 * yOp K ^ p.2)) i j =
      if (i,j) ∈ s then c (i,j) else 0 := by
  rw [pbwCoeff_finiteNormalOrderedSum]
  by_cases h : (i,j) ∈ s
  · rw [Finset.sum_eq_single (i,j)]
    · simp [h]
    · intro q hq hqne
      have hneq : ¬(i = q.1 ∧ j = q.2) := by
        intro he
        apply hqne
        exact Prod.ext he.1.symm he.2.symm
      simp [hneq]
    · simp [h]
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    have hneq : ¬(i = q.1 ∧ j = q.2) := by
      intro he
      apply h
      have hqp : q = (i,j) := Prod.ext he.1.symm he.2.symm
      simpa [hqp] using hq
    simp [hneq]

theorem finiteNormalOrderedSum_injective
    (s : Finset (ℕ × ℕ)) (c d : ℕ × ℕ → K)
    (h : (∑ p ∈ s, c p • (xOp K ^ p.1 * yOp K ^ p.2)) =
      ∑ p ∈ s, d p • (xOp K ^ p.1 * yOp K ^ p.2)) :
    ∀ p ∈ s, c p = d p := by
  intro p hp
  have hcoeff := congrArg (fun T => pbwCoeff T p.1 p.2) h
  rw [pbwCoeff_finiteNormalOrderedSum_recovery,
    pbwCoeff_finiteNormalOrderedSum_recovery] at hcoeff
  cases p with
  | mk i j => simpa [hp] using hcoeff

end PBWCoefficientInversion

/-- A normal-ordered PBW monomial, with all powers of `X` to the left of powers of `Y`. -/
noncomputable def normalOrderedMonomial (a b : ℕ) : Module.End K K[X] :=
  xOp K ^ a * yOp K ^ b

/-- The linear span of the normal-ordered PBW monomials in `End_K(K[X])`. -/
noncomputable def normalOrderedSpan : Submodule K (Module.End K K[X]) :=
  Submodule.span K (Set.range fun p : ℕ × ℕ => normalOrderedMonomial (K := K) p.1 p.2)

/-- The product of two normal-ordered monomials is a finite linear combination of such
monomials. The coefficient is the number of ways to commute `k` derivatives past powers of
`X`. -/
theorem normalOrdered_mul (a b c d : ℕ) :
    normalOrderedMonomial (K := K) a b * normalOrderedMonomial c d =
      ∑ k ∈ range (min c b).succ,
        (b.choose k * c.descFactorial k : K) •
          normalOrderedMonomial (K := K) (a + c-k) (b + d-k) := by
  calc
    _ = xOp K ^ a * (yOp K ^ b * (xOp K ^ c * yOp K ^ d)) := by exact mul_assoc _ _ _
    _ = xOp K ^ a * ((yOp K ^ b * xOp K ^ c) * yOp K ^ d) := by congr 1
    _ = xOp K ^ a * (yOp K ^ b * xOp K ^ c) * yOp K ^ d := by
      exact (mul_assoc (xOp K ^ a) (yOp K ^ b * xOp K ^ c) (yOp K ^ d)).symm
    _ = xOp K ^ a *
        (∑ k ∈ range (min c b).succ,
          (b.choose k * c.descFactorial k : K) •
            (xOp K ^ (c-k) * yOp K ^ (b-k))) * yOp K ^ d := by
      rw [yOp_pow_mul_xOp_pow]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine sum_congr rfl ?_
      intro k hk
      have hkmin : k ≤ min c b := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hkb : k ≤ b := hkmin.trans (min_le_right _ _)
      have hkc : k ≤ c := hkmin.trans (min_le_left _ _)
      rw [mul_smul_comm, smul_mul_assoc]
      have hX : a + (c-k) = a+c-k := by omega
      have hY : (b-k)+d = b+d-k := by omega
      simp only [← mul_assoc, ← pow_add, hX]
      rw [mul_assoc, ← pow_add, hY]
      rfl

/-- The exact product expansion for two finite normal-ordered PBW sums. Each contraction is
listed explicitly; later weighted arguments use `ρ + σ > 0` to show that the terms with `k > 0`
lie strictly below the uncontracted weight. -/
theorem finiteNormalOrderedSum_mul
    (c d : (ℕ × ℕ) →₀ K) :
    (c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2)) *
        (d.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2)) =
      ∑ p ∈ c.support, ∑ q ∈ d.support,
        ∑ k ∈ range (min q.1 p.2).succ,
          (c p * d q * (p.2.choose k * q.1.descFactorial k : K)) •
            normalOrderedMonomial (K := K) (p.1+q.1-k) (p.2+q.2-k) := by
  classical
  change
    (∑ p ∈ c.support, c p • normalOrderedMonomial (K := K) p.1 p.2) *
      (∑ q ∈ d.support, d q • normalOrderedMonomial (K := K) q.1 q.2) = _
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine sum_congr rfl ?_
  intro p hp
  refine sum_congr rfl ?_
  intro q hq
  rw [smul_mul_smul_comm, normalOrdered_mul]
  simp only [smul_sum, smul_smul]

private theorem normalOrdered_mul_mem_span (a b c d : ℕ) :
    normalOrderedMonomial (K := K) a b * normalOrderedMonomial c d ∈
      normalOrderedSpan (K := K) := by
  rw [normalOrdered_mul]
  apply sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨(a+c-k, b+d-k), rfl⟩

/-- Multiplying any two elements of the normal-ordered span stays in that span. -/
theorem normalOrderedSpan_mul_self :
    normalOrderedSpan (K := K) * normalOrderedSpan (K := K) ≤ normalOrderedSpan (K := K) := by
  change Submodule.span K (Set.range fun p : ℕ × ℕ => normalOrderedMonomial (K := K) p.1 p.2) *
    Submodule.span K (Set.range fun p : ℕ × ℕ => normalOrderedMonomial (K := K) p.1 p.2) ≤ _
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_mul.mp hz with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨p, rfl⟩
  rcases hv with ⟨q, rfl⟩
  exact normalOrdered_mul_mem_span p.1 p.2 q.1 q.2

private theorem normalOrderedSpan_one :
    (1 : Module.End K K[X]) ∈ normalOrderedSpan (K := K) := by
  apply Submodule.subset_span
  exact ⟨(0,0), by simp [normalOrderedMonomial]⟩

noncomputable def normalOrderedSubalgebra :
    Subalgebra K (Module.End K K[X]) where
  carrier := normalOrderedSpan (K := K)
  add_mem' := Submodule.add_mem _
  mul_mem' := by
    intro a b ha hb
    exact normalOrderedSpan_mul_self (Submodule.mul_mem_mul ha hb)
  algebraMap_mem' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ normalOrderedSpan_one

/-- Each generator of `A1 K` belongs to the normal-ordered span; closure under multiplication then
places the entire generated Weyl subalgebra in that span. -/
theorem A1_le_normalOrderedSpan : (A1 K).toSubmodule ≤ normalOrderedSpan (K := K) := by
  have hadjoin : A1 K ≤ normalOrderedSubalgebra (K := K) := by
    apply Algebra.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change xOp K ∈ normalOrderedSpan (K := K)
      apply Submodule.subset_span
      exact ⟨(1,0), by simp [normalOrderedMonomial]⟩
    · change yOp K ∈ normalOrderedSpan (K := K)
      apply Submodule.subset_span
      exact ⟨(0,1), by simp [normalOrderedMonomial]⟩
  exact hadjoin

/-- Every normal-ordered monomial belongs to the Weyl subalgebra generated by `X` and `Y`. -/
theorem normalOrderedSpan_le_A1 :
    normalOrderedSpan (K := K) ≤ (A1 K).toSubmodule := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨p, rfl⟩
  have hx : xOp K ∈ A1 K := Algebra.subset_adjoin (by simp)
  have hy : yOp K ∈ A1 K := Algebra.subset_adjoin (by simp)
  change (xOp K ^ p.1 * yOp K ^ p.2) ∈ A1 K
  exact mul_mem (pow_mem hx _) (pow_mem hy _)

/-- The normal-ordered monomials span exactly the first Weyl algebra in the operator model. -/
theorem A1_toSubmodule_eq_normalOrderedSpan :
    (A1 K).toSubmodule = normalOrderedSpan (K := K) := by
  apply le_antisymm
  · exact A1_le_normalOrderedSpan
  · exact normalOrderedSpan_le_A1

/-- Every element of the first Weyl algebra has a finite-support normal-ordered PBW expansion.
The finite support is represented canonically by a `Finsupp`. -/
theorem A1_exists_finiteNormalOrderedExpansion (T : A1 K) :
    ∃ c : (ℕ × ℕ) →₀ K,
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        (T : Module.End K K[X]) := by
  have hmem : (T : Module.End K K[X]) ∈ normalOrderedSpan (K := K) := by
    rw [← A1_toSubmodule_eq_normalOrderedSpan]
    exact T.property
  exact (Finsupp.mem_span_range_iff_exists_finsupp).mp hmem

section PBWFinsuppUniqueness

variable [CharZero K]

/-- Coefficient extraction recovers each coordinate of a finite-support PBW expansion. -/
theorem pbwCoeff_finsuppNormalOrderedSum
    (c : (ℕ × ℕ) →₀ K) (i j : ℕ) :
    pbwCoeff (c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2)) i j = c (i,j) := by
  classical
  rw [Finsupp.sum]
  change pbwCoeff (∑ p ∈ c.support, c p • (xOp K ^ p.1 * yOp K ^ p.2)) i j = c (i,j)
  rw [pbwCoeff_finiteNormalOrderedSum]
  by_cases hmem : (i,j) ∈ c.support
  · rw [Finset.sum_eq_single (i,j)]
    · simp
    · intro q hq hqne
      have hneq : ¬(i = q.1 ∧ j = q.2) := by
        intro he
        apply hqne
        exact Prod.ext he.1.symm he.2.symm
      simp [hneq]
    · simp [hmem]
  · have hzero : c (i,j) = 0 := by simpa using hmem
    rw [Finset.sum_eq_zero]
    · simp [hzero]
    · intro q hq
      have hneq : ¬(i = q.1 ∧ j = q.2) := by
        intro he
        apply hmem
        have hqi : q = (i,j) := Prod.ext he.1.symm he.2.symm
        simpa [hqi] using hq
      simp [hneq]

/-- Finite-support normal-ordered PBW expansions are unique over a characteristic-zero field. -/
theorem A1_finiteNormalOrderedExpansion_unique
    (T : A1 K) (c d : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X]))
    (hd : d.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    c = d := by
  ext p
  have hcoeff := congrArg (fun T => pbwCoeff T p.1 p.2) (hc.trans hd.symm)
  rw [pbwCoeff_finsuppNormalOrderedSum, pbwCoeff_finsuppNormalOrderedSum] at hcoeff
  exact hcoeff

end PBWFinsuppUniqueness

/-- The exponent map used by `symbol` is injective on pairs of natural exponents. -/
theorem expo_injective : Function.Injective (fun p : ℕ × ℕ => expo p.1 p.2) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  apply Prod.ext
  · have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    simpa [expo] using h0
  · have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
    simpa [expo] using h1

/-- Every exponent of a bivariate polynomial is represented by a pair of natural exponents. -/
theorem expo_surjective : Function.Surjective (fun p : ℕ × ℕ => expo p.1 p.2) := by
  intro d
  refine ⟨(d 0, d 1), ?_⟩
  ext i
  fin_cases i <;> simp [expo]

/-- The weighted degree of a PBW exponent is the expected linear combination of its two
coordinates. -/
theorem expo_weight (ρ σ : ℤ) (i j : ℕ) :
    Finsupp.weight (wt ρ σ) (expo i j) = (i : ℤ) * ρ + (j : ℤ) * σ := by
  simp [expo, wt, Finsupp.weight_single]

/-- The `k`-th contraction in a normal-ordered product lowers its exponent weight by exactly
`k (ρ + σ)`. The hypothesis records that the natural-number subtractions in the contraction are
defined without truncation. -/
theorem normalOrdered_contraction_weight (ρ σ : ℤ) (a b c d k : ℕ)
    (hk : k ≤ min c b) :
    Finsupp.weight (wt ρ σ) (expo (a+c-k) (b+d-k)) + (k : ℤ) * (ρ+σ) =
      Finsupp.weight (wt ρ σ) (expo (a+c) (b+d)) := by
  rw [expo_weight, expo_weight]
  have hkc : k ≤ a+c := (hk.trans (min_le_left _ _)).trans (Nat.le_add_left c a)
  have hkb : k ≤ b+d := (hk.trans (min_le_right _ _)).trans (Nat.le_add_right b d)
  rw [Nat.cast_sub hkc, Nat.cast_sub hkb]
  push_cast
  ring

/-- If the direction has positive total weight, every nonzero contraction lowers the exponent
weight strictly. -/
theorem normalOrdered_contraction_weight_lt (ρ σ : ℤ) (hδ : 0 < ρ+σ)
    (a b c d k : ℕ) (hk : k ≤ min c b) (hkpos : 0 < k) :
    Finsupp.weight (wt ρ σ) (expo (a+c-k) (b+d-k)) <
      Finsupp.weight (wt ρ σ) (expo (a+c) (b+d)) := by
  have hweight := normalOrdered_contraction_weight ρ σ a b c d k hk
  have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
  have hprod : (0 : ℤ) < (k : ℤ) * (ρ+σ) := mul_pos hkz hδ
  calc
    _ < _ := lt_add_of_pos_right _ hprod
    _ = _ := hweight

/-- Differentiation lowers the weight of each supported exponent by the variable weight. -/
theorem pderiv_support_weight_le (w : Fin 2 → ℤ) (p : MvPolynomial (Fin 2) K)
    (M : ℤ) (hP : ∀ e ∈ p.support, Finsupp.weight w e ≤ M) (i : Fin 2) :
    ∀ e ∈ (MvPolynomial.pderiv i p).support,
      Finsupp.weight w e ≤ M - w i := by
  intro e he
  have hcoeff := MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hsrc : MvPolynomial.coeff (e + Finsupp.single i 1) p ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz, zero_mul]
  have hsrcmem : e + Finsupp.single i 1 ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr hsrc
  have hbound := hP (e + Finsupp.single i 1) hsrcmem
  have hw : Finsupp.weight w (e + Finsupp.single i 1) =
      Finsupp.weight w e + w i := by
    rw [map_add, Finsupp.weight_single]
    simp
  rw [hw] at hbound
  omega

/-- Differentiation commutes with taking a weighted component, with its shifted weight. -/
theorem pderiv_weightedHomogeneousComponent (w : Fin 2 → ℤ)
    (p : MvPolynomial (Fin 2) K) (M : ℤ) (i : Fin 2) :
    MvPolynomial.pderiv i (MvPolynomial.weightedHomogeneousComponent w M p) =
      MvPolynomial.weightedHomogeneousComponent w (M - w i) (MvPolynomial.pderiv i p) := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_weightedHomogeneousComponent]
  have hw : Finsupp.weight w (d + Finsupp.single i 1) =
      Finsupp.weight w d + w i := by
    rw [map_add, Finsupp.weight_single]
    simp
  have hEq : Finsupp.weight w (d + Finsupp.single i 1) = M ↔
      Finsupp.weight w d = M - w i := by rw [hw]; omega
  simp only [hEq]
  by_cases h : Finsupp.weight w d = M - w i <;> simp [h]

/-- For commutative multivariate polynomials, the top weighted homogeneous component of a
product is the product of the top components, provided the two weighted degrees are specified.
This generic lemma will be applied after the Weyl contraction terms have been shown to lie below
the top weight. -/
theorem weightedComponent_product_at_top
    (w : Fin 2 → ℤ) (p q : MvPolynomial (Fin 2) K) (m n : ℤ)
    (hp : MvPolynomial.weightedTotalDegree' w p = (m : WithBot ℤ))
    (hq : MvPolynomial.weightedTotalDegree' w q = (n : WithBot ℤ)) :
    MvPolynomial.weightedHomogeneousComponent w (m+n) (p*q) =
      MvPolynomial.weightedHomogeneousComponent w m p *
        MvPolynomial.weightedHomogeneousComponent w n q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [MvPolynomial.coeff_mul]
  rw [MvPolynomial.coeff_mul]
  simp_rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : Finsupp.weight w d = m+n
  · rw [if_pos hd]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hdiag : Finsupp.weight w x.1 + Finsupp.weight w x.2 = Finsupp.weight w d := by
      calc
        _ = Finsupp.weight w (x.1 + x.2) := by rw [map_add]
        _ = Finsupp.weight w d := by rw [Finset.mem_antidiagonal.mp hx]
    by_cases h1 : p.coeff x.1 = 0
    · simp [h1]
    by_cases h2 : q.coeff x.2 = 0
    · simp [h2]
    have hxs : x.1 ∈ p.support := MvPolynomial.mem_support_iff.mpr h1
    have hys : x.2 ∈ q.support := MvPolynomial.mem_support_iff.mpr h2
    have hxm : Finsupp.weight w x.1 ≤ m := by
      have hle : (Finsupp.weight w x.1 : WithBot ℤ) ≤ MvPolynomial.weightedTotalDegree' w p := by
        change (Finsupp.weight w x.1 : WithBot ℤ) ≤
          p.support.sup (fun e => (Finsupp.weight w e : WithBot ℤ))
        exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => (Finsupp.weight w e : WithBot ℤ)) hxs
      rw [hp] at hle
      exact WithBot.coe_le_coe.mp hle
    have hyn : Finsupp.weight w x.2 ≤ n := by
      have hle : (Finsupp.weight w x.2 : WithBot ℤ) ≤ MvPolynomial.weightedTotalDegree' w q := by
        change (Finsupp.weight w x.2 : WithBot ℤ) ≤
          q.support.sup (fun e => (Finsupp.weight w e : WithBot ℤ))
        exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => (Finsupp.weight w e : WithBot ℤ)) hys
      rw [hq] at hle
      exact WithBot.coe_le_coe.mp hle
    have hxeq : Finsupp.weight w x.1 = m := by omega
    have hyeq : Finsupp.weight w x.2 = n := by omega
    simp [hxeq, hyeq]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    by_cases h1 : Finsupp.weight w x.1 = m
    · by_cases h2 : Finsupp.weight w x.2 = n
      · exfalso
        apply hd
        have hdiag : Finsupp.weight w x.1 + Finsupp.weight w x.2 = Finsupp.weight w d := by
          calc
            _ = Finsupp.weight w (x.1 + x.2) := by rw [map_add]
            _ = Finsupp.weight w d := by rw [Finset.mem_antidiagonal.mp hx]
        omega
      · simp [h2]
    · simp [h1]

/-- At a target weight equal to the sum of two support bounds, only top components contribute. -/
theorem weightedComponent_product_of_bounds (w : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) K) (m n : ℤ)
    (hp : ∀ e ∈ p.support, Finsupp.weight w e ≤ m)
    (hq : ∀ e ∈ q.support, Finsupp.weight w e ≤ n) :
    MvPolynomial.weightedHomogeneousComponent w (m+n) (p*q) =
      MvPolynomial.weightedHomogeneousComponent w m p *
        MvPolynomial.weightedHomogeneousComponent w n q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [MvPolynomial.coeff_mul]
  rw [MvPolynomial.coeff_mul]
  simp_rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : Finsupp.weight w d = m+n
  · rw [if_pos hd]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hdiag : Finsupp.weight w x.1 + Finsupp.weight w x.2 = Finsupp.weight w d := by
      calc
        _ = Finsupp.weight w (x.1 + x.2) := by rw [map_add]
        _ = Finsupp.weight w d := by rw [Finset.mem_antidiagonal.mp hx]
    by_cases h1 : p.coeff x.1 = 0
    · simp [h1]
    by_cases h2 : q.coeff x.2 = 0
    · simp [h2]
    have hxs : x.1 ∈ p.support := MvPolynomial.mem_support_iff.mpr h1
    have hys : x.2 ∈ q.support := MvPolynomial.mem_support_iff.mpr h2
    have hxeq : Finsupp.weight w x.1 = m := by have := hp x.1 hxs; have := hq x.2 hys; omega
    have hyeq : Finsupp.weight w x.2 = n := by have := hp x.1 hxs; have := hq x.2 hys; omega
    simp [hxeq, hyeq]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    by_cases h1 : Finsupp.weight w x.1 = m
    · by_cases h2 : Finsupp.weight w x.2 = n
      · exfalso
        apply hd
        have hdiag : Finsupp.weight w x.1 + Finsupp.weight w x.2 = Finsupp.weight w d := by
          calc
            _ = Finsupp.weight w (x.1 + x.2) := by rw [map_add]
            _ = Finsupp.weight w d := by rw [Finset.mem_antidiagonal.mp hx]
        omega
      · simp [h2]
    · simp [h1]

/-- The top allowed component of a Poisson bracket is the bracket of the top components. -/
theorem poisson_weightedComponent_of_bounds (w : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) K) (m n : ℤ)
    (hp : ∀ e ∈ p.support, Finsupp.weight w e ≤ m)
    (hq : ∀ e ∈ q.support, Finsupp.weight w e ≤ n) :
    MvPolynomial.weightedHomogeneousComponent w (m+n-(w 0+w 1))
      (poisson p q) =
      poisson (MvPolynomial.weightedHomogeneousComponent w m p)
        (MvPolynomial.weightedHomogeneousComponent w n q) := by
  let pY := MvPolynomial.pderiv 1 p
  let pX := MvPolynomial.pderiv 0 p
  let qY := MvPolynomial.pderiv 1 q
  let qX := MvPolynomial.pderiv 0 q
  have hpy := pderiv_support_weight_le w p m hp 1
  have hpx := pderiv_support_weight_le w p m hp 0
  have hqy := pderiv_support_weight_le w q n hq 1
  have hqx := pderiv_support_weight_le w q n hq 0
  unfold poisson
  rw [map_sub]
  have htarget1 : m+n-(w 0+w 1) = (m-w 1)+(n-w 0) := by omega
  have htarget2 : m+n-(w 0+w 1) = (m-w 0)+(n-w 1) := by omega
  rw [htarget1, weightedComponent_product_of_bounds w pY qX (m-w 1) (n-w 0) hpy hqx]
  rw [← pderiv_weightedHomogeneousComponent w p m 1,
      ← pderiv_weightedHomogeneousComponent w q n 0]
  rw [← htarget1, htarget2,
      weightedComponent_product_of_bounds w pX qY (m-w 0) (n-w 1) hpx hqy]
  rw [← pderiv_weightedHomogeneousComponent w p m 0,
      ← pderiv_weightedHomogeneousComponent w q n 1]

/-- A finite PBW expansion in `A1 K` gives the corresponding finite sum formula for its symbol.
The theorem includes the operator expansion witness so its coefficient map can be reused in support
and filtration arguments. -/
theorem symbol_finiteNormalOrderedExpansion
    [CharZero K] (T : A1 K) :
    ∃ c : (ℕ × ℕ) →₀ K,
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
          (T : Module.End K K[X]) ∧
      symbol (T : Module.End K K[X]) =
        ∑ p ∈ c.support, MvPolynomial.monomial (expo p.1 p.2) (c p) := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  have hcoeff : ∀ i j, pbwCoeff (T : Module.End K K[X]) i j = c (i,j) := by
    intro i j
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  have hsub : Function.support (fun p : ℕ × ℕ =>
      MvPolynomial.monomial (expo p.1 p.2) (pbwCoeff (T : Module.End K K[X]) p.1 p.2)) ⊆ c.support := by
    intro p hp
    apply Finsupp.mem_support_iff.mpr
    have hpcoeff : pbwCoeff (T : Module.End K K[X]) p.1 p.2 ≠ 0 := by
      intro hz
      apply hp
      simp [hz]
    simpa only [hcoeff p.1 p.2] using hpcoeff
  refine ⟨c, hc, ?_⟩
  unfold symbol
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [hcoeff p.1 p.2]

/-- On an element of `A1 K`, the polynomial coefficient of its PBW symbol at `x^i y^j` is the
coefficient extracted by `pbwCoeff`. -/
theorem symbol_coeff_pbwCoeff [CharZero K]
    (T : A1 K) (i j : ℕ) :
    MvPolynomial.coeff (expo i j) (symbol (T : Module.End K K[X])) =
      pbwCoeff (T : Module.End K K[X]) i j := by
  classical
  obtain ⟨c, hc, hsym⟩ := symbol_finiteNormalOrderedExpansion T
  have hcoeff : ∀ i j, pbwCoeff (T : Module.End K K[X]) i j = c (i,j) := by
    intro i j
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  rw [hsym, MvPolynomial.coeff_sum]
  by_cases hmem : (i,j) ∈ c.support
  · rw [Finset.sum_eq_single (i,j)]
    · simp [hcoeff i j]
    · intro q hq hqne
      have hex : expo q.1 q.2 ≠ expo i j := by
        intro he
        apply hqne
        have hp : q = (i,j) := by
          apply Prod.ext
          · have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
            simpa [expo] using this
          · have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
            simpa [expo] using this
        exact hp
      simp [hex]
    · simp [hmem]
  · have hzero : c (i,j) = 0 := by simpa using hmem
    rw [Finset.sum_eq_zero]
    · rw [hcoeff i j, hzero]
    · intro q hq
      have hex : expo q.1 q.2 ≠ expo i j := by
        intro he
        have hp : q = (i,j) := by
          apply Prod.ext
          · have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
            simpa [expo] using this
          · have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
            simpa [expo] using this
        apply hmem
        simpa [hp] using hq
      simp [hex]

/-- The PBW symbol is additive on the Weyl subalgebra. -/
theorem symbol_add [CharZero K]
    (P Q : A1 K) :
    symbol ((P + Q : A1 K) : Module.End K K[X]) =
      symbol (P : Module.End K K[X]) + symbol (Q : Module.End K K[X]) := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective d
  change MvPolynomial.coeff (expo i j)
      (symbol ((P + Q : A1 K) : Module.End K K[X])) =
    MvPolynomial.coeff (expo i j)
      (symbol (P : Module.End K K[X]) + symbol (Q : Module.End K K[X]))
  rw [symbol_coeff_pbwCoeff, MvPolynomial.coeff_add,
    symbol_coeff_pbwCoeff, symbol_coeff_pbwCoeff]
  simp only [Subalgebra.coe_add]
  rw [pbwCoeff_add]

/-- The PBW symbol is homogeneous for scalar multiplication on the Weyl subalgebra. -/
theorem symbol_smul [CharZero K]
    (a : K) (P : A1 K) :
    symbol ((a • P : A1 K) : Module.End K K[X]) =
      a • symbol (P : Module.End K K[X]) := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective d
  change MvPolynomial.coeff (expo i j)
      (symbol ((a • P : A1 K) : Module.End K K[X])) =
    MvPolynomial.coeff (expo i j) (a • symbol (P : Module.End K K[X]))
  rw [symbol_coeff_pbwCoeff, MvPolynomial.coeff_smul,
    symbol_coeff_pbwCoeff]
  simp only [Subalgebra.coe_smul]
  rw [pbwCoeff_smul]
  simp [smul_eq_mul]

/-- The PBW symbol is additive under subtraction on the Weyl subalgebra. -/
theorem symbol_sub [CharZero K]
    (P Q : A1 K) :
    symbol ((P - Q : A1 K) : Module.End K K[X]) =
      symbol (P : Module.End K K[X]) - symbol (Q : Module.End K K[X]) := by
  have hneg : symbol ((-Q : A1 K) : Module.End K K[X]) =
      -symbol (Q : Module.End K K[X]) := by
    have hsmul : (-1 : K) • Q = -Q := by exact neg_one_smul K Q
    have hneg_smul := symbol_smul (-1 : K) Q
    rw [hsmul] at hneg_smul
    simpa only [neg_one_smul K] using hneg_smul
  calc
    symbol ((P - Q : A1 K) : Module.End K K[X]) =
        symbol ((P + (-Q) : A1 K) : Module.End K K[X]) := by rfl
    _ = symbol (P : Module.End K K[X]) +
        symbol ((-Q : A1 K) : Module.End K K[X]) := symbol_add P (-Q)
    _ = symbol (P : Module.End K K[X]) - symbol (Q : Module.End K K[X]) := by
      rw [hneg, sub_eq_add_neg]

/-- The support of the PBW symbol is exactly the image of the finite set of nonzero PBW
coefficients. Thus the weighted support on which the Newton analysis operates is genuinely finite. -/
theorem symbol_support_eq_pbwCoefficientImage [CharZero K]
    (T : A1 K) :
    ∃ c : (ℕ × ℕ) →₀ K,
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        (T : Module.End K K[X]) ∧
      (symbol (T : Module.End K K[X])).support =
        c.support.image (fun p => expo p.1 p.2) := by
  classical
  obtain ⟨c, hc, hsym⟩ := symbol_finiteNormalOrderedExpansion T
  have hcoeff : ∀ i j, pbwCoeff (T : Module.End K K[X]) i j = c (i,j) := by
    intro i j
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  refine ⟨c, hc, ?_⟩
  apply Finset.ext
  intro m
  constructor
  · intro hm
    have hm' : m ∈ (∑ p ∈ c.support,
        MvPolynomial.monomial (expo p.1 p.2) (c p)).support := by rw [← hsym]; exact hm
    have hsubset := MvPolynomial.support_sum
      (s := c.support) (f := fun p => MvPolynomial.monomial (expo p.1 p.2) (c p))
    have hm'' := hsubset hm'
    simp only [Finset.mem_biUnion] at hm''
    rcases hm'' with ⟨p, hp, hpm⟩
    have hcne : c p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hmono : (MvPolynomial.monomial (expo p.1 p.2) (c p)).support =
        {expo p.1 p.2} := by
      rw [MvPolynomial.support_monomial]
      simp [hcne]
    rw [hmono] at hpm
    have hpm' : m = expo p.1 p.2 := by simpa using hpm
    exact Finset.mem_image.mpr ⟨p, hp, hpm'.symm⟩
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
    rw [MvPolynomial.mem_support_iff]
    rw [symbol_coeff_pbwCoeff]
    rw [hcoeff p.1 p.2]
    exact Finsupp.mem_support_iff.mp hp

/-- The operator's mass is the number of distinct grades occurring among its nonzero PBW
coefficients. -/
noncomputable def pbwOperatorLinear :
    ((ℕ × ℕ) →₀ K) →ₗ[K] Module.End K K[X] :=
  Finsupp.linearCombination K
    (fun p : ℕ × ℕ => normalOrderedMonomial (K := K) p.1 p.2)

noncomputable def pbwPolynomialLinear :
    ((ℕ × ℕ) →₀ K) →ₗ[K] MvPolynomial (Fin 2) K :=
  Finsupp.linearCombination K
    (fun p : ℕ × ℕ => MvPolynomial.monomial (expo p.1 p.2) (1 : K))

noncomputable def pbwProductCoeff (c d : (ℕ × ℕ) →₀ K) : (ℕ × ℕ) →₀ K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    ∑ k ∈ range (min q.1 p.2).succ,
      Finsupp.single (p.1 + q.1 - k, p.2 + q.2 - k)
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))

private theorem pbwOperatorLinear_eq_sum (c : (ℕ × ℕ) →₀ K) :
    pbwOperatorLinear (K := K) c =
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) := by
  simp [pbwOperatorLinear, Finsupp.linearCombination_apply]

private theorem pbwProductCoeff_operator (c d : (ℕ × ℕ) →₀ K) :
    pbwOperatorLinear (K := K) (pbwProductCoeff (K := K) c d) =
      pbwOperatorLinear c * pbwOperatorLinear d := by
  classical
  rw [pbwOperatorLinear_eq_sum (c := pbwProductCoeff c d),
    pbwOperatorLinear_eq_sum (c := c), pbwOperatorLinear_eq_sum (c := d)]
  rw [finiteNormalOrderedSum_mul]
  change Finsupp.linearCombination K
    (fun p : ℕ × ℕ => normalOrderedMonomial (K := K) p.1 p.2)
    (pbwProductCoeff (K := K) c d) = _
  simp [pbwProductCoeff, Finsupp.linearCombination_single]

private theorem pbwPolynomialLinear_eq_sum (c : (ℕ × ℕ) →₀ K) :
    pbwPolynomialLinear (K := K) c =
      c.sum (fun p a => MvPolynomial.monomial (expo p.1 p.2) a) := by
  simp [pbwPolynomialLinear, Finsupp.linearCombination_apply, MvPolynomial.smul_monomial]

private theorem pbwProductCoeff_polynomial (c d : (ℕ × ℕ) →₀ K) :
    pbwPolynomialLinear (K := K) (pbwProductCoeff (K := K) c d) =
      ∑ p ∈ c.support, ∑ q ∈ d.support,
        ∑ k ∈ range (min q.1 p.2).succ,
          MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
            (c p * d q * (p.2.choose k * q.1.descFactorial k : K)) := by
  classical
  change Finsupp.linearCombination K
    (fun p : ℕ × ℕ => MvPolynomial.monomial (expo p.1 p.2) (1 : K))
    (pbwProductCoeff (K := K) c d) = _
  rw [pbwProductCoeff]
  simp only [map_sum, Finsupp.linearCombination_single, MvPolynomial.smul_monomial]
  simp [smul_eq_mul]

private theorem expo_add (a b c d : ℕ) :
    expo (a + c) (b + d) = expo a b + expo c d := by
  ext i
  fin_cases i <;> simp [expo]

private theorem weightedComponent_monomial (w : Fin 2 → ℤ) (n : ℤ)
    (d : Fin 2 →₀ ℕ) (a : K) :
    MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.monomial d a) =
      if Finsupp.weight w d = n then MvPolynomial.monomial d a else 0 := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases h : Finsupp.weight w d = n
  · rw [if_pos h]
    by_cases he : d = e
    · subst e
      simp [h, MvPolynomial.coeff_monomial]
    · simp [he, MvPolynomial.coeff_monomial]
  · rw [if_neg h]
    by_cases he : d = e
    · subst e
      simp [h]
    · simp [he, MvPolynomial.coeff_monomial]

noncomputable def pbwProductPoly (c d : (ℕ × ℕ) →₀ K) : MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    ∑ k ∈ range (min q.1 p.2).succ,
      MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))

noncomputable def pbwPolynomial (c : (ℕ × ℕ) →₀ K) : MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support,
    MvPolynomial.monomial (expo p.1 p.2) (c p)

noncomputable def pbwCorrectionPoly (c d : (ℕ × ℕ) →₀ K) :
    MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    ∑ k ∈ range (min q.1 p.2).succ with 0 < k,
      MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))

noncomputable def pbwFirstContractionPoly (c d : (ℕ × ℕ) →₀ K) :
    MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    MvPolynomial.monomial (expo (p.1 + q.1 - 1) (p.2 + q.2 - 1))
      (c p * d q * (p.2 : K) * (q.1 : K))

noncomputable def pbwFirstContractionKOnePoly (c d : (ℕ × ℕ) →₀ K) :
    MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    ∑ k ∈ range (min q.1 p.2).succ with k = 1,
      MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))

noncomputable def pbwHigherCorrectionPoly (c d : (ℕ × ℕ) →₀ K) :
    MvPolynomial (Fin 2) K :=
  ∑ p ∈ c.support, ∑ q ∈ d.support,
    ∑ k ∈ range (min q.1 p.2).succ with 1 < k,
      MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))

private theorem sum_range_succ_eq_zero_add_pos {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    (∑ k ∈ range n.succ, f k) = f 0 + ∑ k ∈ range n.succ with 0 < k, f k := by
  have hpart := Finset.sum_filter_add_sum_filter_not
    (range n.succ) (fun k : ℕ => 0 < k) f
  have hzero : (∑ k ∈ range n.succ with ¬ 0 < k, f k) = f 0 := by simp
  calc
    (∑ k ∈ range n.succ, f k) =
        (∑ k ∈ range n.succ with 0 < k, f k) +
          (∑ k ∈ range n.succ with ¬ 0 < k, f k) := hpart.symm
    _ = (∑ k ∈ range n.succ with 0 < k, f k) + f 0 := by rw [hzero]
    _ = f 0 + ∑ k ∈ range n.succ with 0 < k, f k := by ac_rfl

private theorem sum_range_succ_pos_eq_one_add_gt_one {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    (∑ k ∈ range n.succ with 0 < k, f k) =
      (∑ k ∈ range n.succ with k = 1, f k) +
        (∑ k ∈ range n.succ with 1 < k, f k) := by
  classical
  have hpart := Finset.sum_filter_add_sum_filter_not
    ((range n.succ).filter (fun k => 0 < k)) (fun k => k = 1) f
  have hfirst : ((range n.succ).filter (fun k => 0 < k)).filter (fun k => k = 1) =
      (range n.succ).filter (fun k => k = 1) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hr, _⟩, heq⟩
      exact ⟨hr, heq⟩
    · rintro ⟨hr, heq⟩
      exact ⟨⟨hr, by omega⟩, heq⟩
  have hhigh : ((range n.succ).filter (fun k => 0 < k)).filter (fun k => ¬ k = 1) =
      (range n.succ).filter (fun k => 1 < k) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hr, hpos⟩, hne⟩
      exact ⟨hr, by omega⟩
    · rintro ⟨hr, hhigh⟩
      exact ⟨⟨hr, by omega⟩, by omega⟩
  rw [hfirst, hhigh] at hpart
  exact hpart.symm

private theorem pbwProductPoly_split (c d : (ℕ × ℕ) →₀ K) :
    pbwProductPoly (K := K) c d =
      (∑ p ∈ c.support, ∑ q ∈ d.support,
        MvPolynomial.monomial (expo (p.1 + q.1) (p.2 + q.2)) (c p * d q)) +
      pbwCorrectionPoly (K := K) c d := by
  classical
  unfold pbwProductPoly pbwCorrectionPoly
  simp_rw [sum_range_succ_eq_zero_add_pos]
  simp_rw [Finset.sum_add_distrib]
  simp

private theorem pbwCorrectionPoly_top_eq_zero (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m + n)
      (pbwCorrectionPoly (K := K) c d) = 0 := by
  classical
  rw [pbwCorrectionPoly]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  apply Finset.sum_eq_zero
  intro k hk
  rw [weightedComponent_monomial]
  have hmem := Finset.mem_filter.mp hk
  have hkRange : k ∈ range (min q.1 p.2).succ := hmem.1
  have hkpos : 0 < k := hmem.2
  have hkmin : k ≤ min q.1 p.2 := Nat.lt_succ_iff.mp (mem_range.mp hkRange)
  have hdrop := normalOrdered_contraction_weight_lt ρ σ hpos
    p.1 p.2 q.1 q.2 k hkmin hkpos
  have hbase : Finsupp.weight (wt ρ σ) (expo (p.1 + q.1) (p.2 + q.2)) ≤ m + n := by
    rw [expo_add, map_add]
    exact add_le_add (hc p hp) (hd q hq)
  have hlow :
      Finsupp.weight (wt ρ σ) (expo (p.1 + q.1 - k) (p.2 + q.2 - k)) < m + n :=
    lt_of_lt_of_le hdrop hbase
  simp [ne_of_lt hlow]

private theorem pbwHigherCorrectionPoly_top_eq_zero (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m+n-(ρ+σ))
      (pbwHigherCorrectionPoly (K := K) c d) = 0 := by
  classical
  rw [pbwHigherCorrectionPoly]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  apply Finset.sum_eq_zero
  intro k hk
  rw [weightedComponent_monomial]
  have hmem := Finset.mem_filter.mp hk
  have hkRange : k ∈ range (min q.1 p.2).succ := hmem.1
  have hkgt : 1 < k := hmem.2
  have hkmin : k ≤ min q.1 p.2 := Nat.lt_succ_iff.mp (mem_range.mp hkRange)
  have hweight := normalOrdered_contraction_weight ρ σ p.1 p.2 q.1 q.2 k hkmin
  have hbase : Finsupp.weight (wt ρ σ) (expo (p.1 + q.1) (p.2 + q.2)) ≤ m + n := by
    rw [expo_add, map_add]
    exact add_le_add (hc p hp) (hd q hq)
  have hkz : (1 : ℤ) < (k : ℤ) := by exact_mod_cast hkgt
  have hmult : ρ + σ < (k : ℤ) * (ρ + σ) := by
    simpa using mul_lt_mul_of_pos_right hkz hpos
  have hlow :
      Finsupp.weight (wt ρ σ) (expo (p.1 + q.1 - k) (p.2 + q.2 - k)) < m+n-(ρ+σ) := by
    omega
  simp [ne_of_lt hlow]

private theorem uncontractedPoly_eq_mul (c d : (ℕ × ℕ) →₀ K) :
    (∑ p ∈ c.support, ∑ q ∈ d.support,
      MvPolynomial.monomial (expo (p.1 + q.1) (p.2 + q.2)) (c p * d q)) =
      pbwPolynomial (K := K) c * pbwPolynomial d := by
  classical
  rw [pbwPolynomial, pbwPolynomial, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine sum_congr rfl ?_
  intro p hp
  refine sum_congr rfl ?_
  intro q hq
  rw [MvPolynomial.monomial_mul, expo_add]

private theorem expo_sub_y (i j : ℕ) :
    expo i j - Finsupp.single 1 1 = expo i (j-1) := by
  ext k
  fin_cases k <;> simp [expo]

private theorem expo_sub_x (i j : ℕ) :
    expo i j - Finsupp.single 0 1 = expo (i-1) j := by
  ext k
  fin_cases k <;> simp [expo]

private theorem pderiv_monomial_y (i j : ℕ) (a : K) :
    MvPolynomial.pderiv 1 (MvPolynomial.monomial (expo i j) a) =
      MvPolynomial.monomial (expo i (j-1)) (a * (j : K)) := by
  rw [MvPolynomial.pderiv_monomial, expo_sub_y]
  congr 1
  simp [expo]

private theorem pderiv_monomial_x (i j : ℕ) (a : K) :
    MvPolynomial.pderiv 0 (MvPolynomial.monomial (expo i j) a) =
      MvPolynomial.monomial (expo (i-1) j) (a * (i : K)) := by
  rw [MvPolynomial.pderiv_monomial, expo_sub_x]
  congr 1
  simp [expo]

private theorem pderiv_pbwPolynomial_y (c : (ℕ × ℕ) →₀ K) :
    MvPolynomial.pderiv 1 (pbwPolynomial (K := K) c) =
      ∑ p ∈ c.support,
        MvPolynomial.monomial (expo p.1 (p.2-1)) (c p * (p.2 : K)) := by
  classical
  rw [pbwPolynomial]
  simp_rw [map_sum, pderiv_monomial_y]

private theorem pderiv_pbwPolynomial_x (c : (ℕ × ℕ) →₀ K) :
    MvPolynomial.pderiv 0 (pbwPolynomial (K := K) c) =
      ∑ p ∈ c.support,
        MvPolynomial.monomial (expo (p.1-1) p.2) (c p * (p.1 : K)) := by
  classical
  rw [pbwPolynomial]
  simp_rw [map_sum, pderiv_monomial_x]

/-- The first contraction in the PBW product of two coefficient arrays is the ordinary first
derivative term. Taking its antisymmetric part gives the Poisson bracket for `[Y,X]=1`. -/
theorem pbwFirstContraction_eq_derivative_product (c d : (ℕ × ℕ) →₀ K) :
    pbwFirstContractionPoly (K := K) c d =
      MvPolynomial.pderiv 1 (pbwPolynomial (K := K) c) *
        MvPolynomial.pderiv 0 (pbwPolynomial (K := K) d) := by
  classical
  rw [pderiv_pbwPolynomial_y, pderiv_pbwPolynomial_x, pbwFirstContractionPoly]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hj : 0 < p.2
  · by_cases hi : 0 < q.1
    · rw [MvPolynomial.monomial_mul]
      have hexp : expo p.1 (p.2-1) + expo (q.1-1) q.2 =
          expo (p.1+q.1-1) (p.2+q.2-1) := by
        ext k
        fin_cases k <;> simp [expo] <;> omega
      rw [hexp]
      congr 1
      ring
    · have hq1 : q.1 = 0 := Nat.eq_zero_of_not_pos hi
      simp [MvPolynomial.monomial_eq, hq1]
  · have hp2 : p.2 = 0 := Nat.eq_zero_of_not_pos hj
    simp [MvPolynomial.monomial_eq, hp2]

theorem pbwFirstContraction_sub_eq_poisson (c d : (ℕ × ℕ) →₀ K) :
    pbwFirstContractionPoly (K := K) c d - pbwFirstContractionPoly (K := K) d c =
      poisson (pbwPolynomial (K := K) c) (pbwPolynomial (K := K) d) := by
  rw [pbwFirstContraction_eq_derivative_product, pbwFirstContraction_eq_derivative_product]
  unfold poisson
  ring

private theorem pbwFirstContractionKOne_pair (p q : ℕ × ℕ) (a b : K) :
    (∑ k ∈ range (min q.1 p.2).succ with k = 1,
      MvPolynomial.monomial (expo (p.1+q.1-k) (p.2+q.2-k))
        (a*b*(p.2.choose k*q.1.descFactorial k : K))) =
      MvPolynomial.monomial (expo (p.1+q.1-1) (p.2+q.2-1))
        (a*b*(p.2 : K)*(q.1 : K)) := by
  classical
  by_cases h : 1 ≤ min q.1 p.2
  · have hs : (range (min q.1 p.2).succ).filter (fun k => k = 1) = {1} := by
      ext k
      simp only [Finset.mem_filter, mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · intro hk
        subst k
        constructor
        · omega
        · rfl
    rw [hs, sum_singleton]
    simp [Nat.choose_one_right, mul_assoc]
  · have h0 : min q.1 p.2 = 0 := by omega
    have hparts : q.1 = 0 ∨ p.2 = 0 := by omega
    rw [h0]
    have hsum : (∑ k ∈ range (0:ℕ).succ with k = 1,
        MvPolynomial.monomial (expo (p.1+q.1-k) (p.2+q.2-k))
          (a*b*(p.2.choose k*q.1.descFactorial k : K)) : MvPolynomial (Fin 2) K) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, mem_range] at hk
      omega
    change (∑ k ∈ range (0:ℕ).succ with k = 1,
        MvPolynomial.monomial (expo (p.1+q.1-k) (p.2+q.2-k))
          (a*b*(p.2.choose k*q.1.descFactorial k : K))) = _
    rw [hsum]
    rcases hparts with hq | hp
    · simp [hq]
    · simp [hp]

private theorem pbwFirstContractionKOne_eq_poly (c d : (ℕ × ℕ) →₀ K) :
    pbwFirstContractionKOnePoly (K := K) c d = pbwFirstContractionPoly (K := K) c d := by
  classical
  unfold pbwFirstContractionKOnePoly pbwFirstContractionPoly
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact pbwFirstContractionKOne_pair p q (c p) (d q)

private theorem pbwCorrectionPoly_eq_first_add_higher (c d : (ℕ × ℕ) →₀ K) :
    pbwCorrectionPoly (K := K) c d =
      pbwFirstContractionPoly (K := K) c d + pbwHigherCorrectionPoly (K := K) c d := by
  classical
  calc
    pbwCorrectionPoly (K := K) c d =
        pbwFirstContractionKOnePoly (K := K) c d +
          pbwHigherCorrectionPoly (K := K) c d := by
      unfold pbwCorrectionPoly pbwFirstContractionKOnePoly pbwHigherCorrectionPoly
      simp_rw [sum_range_succ_pos_eq_one_add_gt_one]
      simp_rw [Finset.sum_add_distrib]
    _ = pbwFirstContractionPoly (K := K) c d +
          pbwHigherCorrectionPoly (K := K) c d := by
      rw [pbwFirstContractionKOne_eq_poly]

/-- The antisymmetric PBW convolution is the Poisson bracket plus contractions of order at
least two. This is an exact polynomial identity, before taking any weighted component. -/
theorem pbwProductPoly_commutator_eq (c d : (ℕ × ℕ) →₀ K) :
    pbwProductPoly (K := K) c d - pbwProductPoly (K := K) d c =
      poisson (pbwPolynomial (K := K) c) (pbwPolynomial (K := K) d) +
        (pbwHigherCorrectionPoly (K := K) c d -
          pbwHigherCorrectionPoly (K := K) d c) := by
  rw [pbwProductPoly_split, pbwProductPoly_split,
    uncontractedPoly_eq_mul, uncontractedPoly_eq_mul,
    pbwCorrectionPoly_eq_first_add_higher, pbwCorrectionPoly_eq_first_add_higher]
  rw [← pbwFirstContraction_sub_eq_poisson c d]
  ring

private theorem pbwPolynomial_support_weight_le (ρ σ m : ℤ)
    (c : (ℕ × ℕ) →₀ K)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m) :
    ∀ e ∈ (pbwPolynomial (K := K) c).support,
      Finsupp.weight (wt ρ σ) e ≤ m := by
  classical
  intro e he
  rw [pbwPolynomial] at he
  have he' := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he'
  rcases he' with ⟨p, hp, hmono⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hmono
  have hexp : e = expo p.1 p.2 := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  subst e
  exact hc p hp

/-- At the first possible commutator weight, every higher PBW contraction vanishes, leaving
the Poisson bracket of the weighted leading components. -/
theorem pbwProductPoly_commutator_top (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m+n-(ρ+σ))
      (pbwProductPoly (K := K) c d - pbwProductPoly (K := K) d c) =
    poisson (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m (pbwPolynomial c))
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) n (pbwPolynomial d)) := by
  have hhighDC : MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
      (m+n-(ρ+σ)) (pbwHigherCorrectionPoly (K := K) d c) = 0 := by
    simpa only [add_comm n m] using
      (pbwHigherCorrectionPoly_top_eq_zero ρ σ n m d c hpos hd hc)
  rw [pbwProductPoly_commutator_eq, map_add, map_sub,
    pbwHigherCorrectionPoly_top_eq_zero ρ σ m n c d hpos hc hd, hhighDC]
  simp only [sub_self, add_zero]
  have hcp := pbwPolynomial_support_weight_le ρ σ m c hc
  have hdp := pbwPolynomial_support_weight_le ρ σ n d hd
  convert poisson_weightedComponent_of_bounds (wt ρ σ)
    (pbwPolynomial c) (pbwPolynomial d) m n hcp hdp using 1; simp [wt]

private theorem pbwProductPoly_top (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n)
    (hp : MvPolynomial.weightedTotalDegree' (wt ρ σ) (pbwPolynomial (K := K) c) = (m : WithBot ℤ))
    (hq : MvPolynomial.weightedTotalDegree' (wt ρ σ) (pbwPolynomial (K := K) d) = (n : WithBot ℤ)) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m + n)
      (pbwProductPoly (K := K) c d) =
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m (pbwPolynomial c) *
      MvPolynomial.weightedHomogeneousComponent (wt ρ σ) n (pbwPolynomial d) := by
  rw [pbwProductPoly_split, map_add,
    pbwCorrectionPoly_top_eq_zero ρ σ m n c d hpos hc hd, uncontractedPoly_eq_mul]
  simpa using weightedComponent_product_at_top
    (wt ρ σ) (pbwPolynomial c) (pbwPolynomial d) m n hp hq

private theorem pbwPolynomialLinear_eq_pbwPolynomial (c : (ℕ × ℕ) →₀ K) :
    pbwPolynomialLinear (K := K) c = pbwPolynomial (K := K) c := by
  rw [pbwPolynomialLinear_eq_sum, Finsupp.sum, pbwPolynomial]

private theorem symbol_eq_pbwPolynomial_of_expansion [CharZero K]
    (T : A1 K) (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    symbol (T : Module.End K K[X]) = pbwPolynomial (K := K) c := by
  obtain ⟨d, hd, hsymbol⟩ := symbol_finiteNormalOrderedExpansion T
  have hdc : d = c := A1_finiteNormalOrderedExpansion_unique T d c hd hc
  rw [hsymbol, hdc]
  rfl

private theorem pbwProductPoly_eq_polynomialLinear (c d : (ℕ × ℕ) →₀ K) :
    pbwProductPoly (K := K) c d = pbwPolynomialLinear (K := K) (pbwProductCoeff c d) := by
  symm
  rw [pbwProductCoeff_polynomial]
  rfl

private theorem symbol_mul_eq_pbwProductPoly_of_expansions [CharZero K]
    (P Q : A1 K) (c d : (ℕ × ℕ) →₀ K)
    (hPexp : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (P : Module.End K K[X]))
    (hQexp : d.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (Q : Module.End K K[X])) :
    symbol ((P * Q : A1 K) : Module.End K K[X]) =
      pbwProductPoly (K := K) c d := by
  have hproductExpansion :
      (pbwProductCoeff (K := K) c d).sum
          (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        ((P * Q : A1 K) : Module.End K K[X]) := by
    calc
      _ = pbwOperatorLinear (K := K) (pbwProductCoeff c d) :=
        (pbwOperatorLinear_eq_sum (pbwProductCoeff c d)).symm
      _ = pbwOperatorLinear c * pbwOperatorLinear d := pbwProductCoeff_operator c d
      _ = (P : Module.End K K[X]) * (Q : Module.End K K[X]) := by
        rw [pbwOperatorLinear_eq_sum c, pbwOperatorLinear_eq_sum d, hPexp, hQexp]
      _ = _ := rfl
  rw [symbol_eq_pbwPolynomial_of_expansion (P * Q : A1 K)
    (pbwProductCoeff c d) hproductExpansion]
  exact (pbwPolynomialLinear_eq_pbwPolynomial (pbwProductCoeff c d)).symm.trans
    (pbwProductPoly_eq_polynomialLinear c d).symm

/-- Every PBW monomial in a Weyl product has grade equal to the sum of the grades of source
monomials. The exact PBW product expansion records witnesses for the two source exponents;
normal-ordering contractions subtract the same integer from both coordinates and preserve grade. -/
theorem symbol_mul_grade_decomposition [CharZero K]
    (P Q : A1 K) :
    ∀ e ∈ (symbol ((P * Q : A1 K) : Module.End K K[X])).support,
      ∃ d ∈ (symbol (P : Module.End K K[X])).support,
        ∃ f ∈ (symbol (Q : Module.End K K[X])).support,
          grade e = grade d + grade f := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hprod := symbol_mul_eq_pbwProductPoly_of_expansions P Q c d hPexp hQexp
  rw [hprod] at *
  intro e he
  have hpqk := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at hpqk
  rcases hpqk with ⟨p, hp, hpqk⟩
  have hqk := MvPolynomial.support_sum hpqk
  simp only [Finset.mem_biUnion] at hqk
  rcases hqk with ⟨q, hq, hk⟩
  have hk' := MvPolynomial.support_sum hk
  simp only [Finset.mem_biUnion] at hk'
  rcases hk' with ⟨k, hk, hmono⟩
  have hcoef : MvPolynomial.coeff e
      (MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmono
  have heq : e = expo (p.1 + q.1 - k) (p.2 + q.2 - k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoef
    exact hcoef rfl
  have hpgrade : grade (expo p.1 p.2) = (p.1 : ℤ) - p.2 := by
    simp [grade, expo]
  have hqgrade : grade (expo q.1 q.2) = (q.1 : ℤ) - q.2 := by
    simp [grade, expo]
  have hkmin : k ≤ min q.1 p.2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hgrade : grade (expo (p.1 + q.1 - k) (p.2 + q.2 - k)) =
      ((p.1 : ℤ) - p.2) + ((q.1 : ℤ) - q.2) := by
    simp [grade, expo]
    rw [Nat.cast_sub (by omega : k ≤ p.1 + q.1),
      Nat.cast_sub (by omega : k ≤ p.2 + q.2)]
    push_cast
    ring
  refine ⟨expo p.1 p.2, ?_, expo q.1 q.2, ?_, ?_⟩
  · rw [hPsupport]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · rw [hQsupport]
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  rw [heq, hgrade, hpgrade, hqgrade]

/-- The PBW grade of a Weyl product is bounded by the sum of the largest grades of its
factors. This is the support-cone consequence of `symbol_mul_grade_decomposition`. -/
theorem symbol_mul_grade_le [CharZero K]
    (P Q : A1 K) (m n : ℤ)
    (hP : ∀ e ∈ (symbol (P : Module.End K K[X])).support, grade e ≤ m)
    (hQ : ∀ e ∈ (symbol (Q : Module.End K K[X])).support, grade e ≤ n) :
    ∀ e ∈ (symbol ((P * Q : A1 K) : Module.End K K[X])).support,
      grade e ≤ m + n := by
  intro e he
  obtain ⟨d, hd, f, hf, hgrade⟩ := symbol_mul_grade_decomposition P Q e he
  rw [hgrade]
  exact add_le_add (hP d hd) (hQ f hf)

/-- The top weighted component of a Weyl product is the product of the top components of its
factors whenever the direction has positive total weight. Every positive PBW contraction then
lies strictly below the sum of the two weighted degrees. -/
theorem symbol_mul_top_component [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ)) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m + n)
      (symbol ((P * Q : A1 K) : Module.End K K[X])) =
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m
      (symbol (P : Module.End K K[X])) *
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) n
      (symbol (Q : Module.End K K[X])) := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hPsymbol : symbol (P : Module.End K K[X]) = pbwPolynomial (K := K) c :=
    symbol_eq_pbwPolynomial_of_expansion P c hPexp
  have hQsymbol : symbol (Q : Module.End K K[X]) = pbwPolynomial (K := K) d :=
    symbol_eq_pbwPolynomial_of_expansion Q d hQexp
  have hc : ∀ p ∈ c.support,
      Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m := by
    intro p hp
    have hmem : expo p.1 p.2 ∈ (symbol (P : Module.End K K[X])).support := by
      rw [hPsupport]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hle : (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol (P : Module.End K K[X])) := by
      change (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
        ((symbol (P : Module.End K K[X])).support).sup
          (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
      exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hmem
    rw [hPdeg] at hle
    exact WithBot.coe_le_coe.mp hle
  have hd : ∀ q ∈ d.support,
      Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n := by
    intro q hq
    have hmem : expo q.1 q.2 ∈ (symbol (Q : Module.End K K[X])).support := by
      rw [hQsupport]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hle : (Finsupp.weight (wt ρ σ) (expo q.1 q.2) : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol (Q : Module.End K K[X])) := by
      change (Finsupp.weight (wt ρ σ) (expo q.1 q.2) : WithBot ℤ) ≤
        ((symbol (Q : Module.End K K[X])).support).sup
          (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
      exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hmem
    rw [hQdeg] at hle
    exact WithBot.coe_le_coe.mp hle
  have hPpolyDeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (pbwPolynomial (K := K) c) = (m : WithBot ℤ) := by rw [← hPsymbol, hPdeg]
  have hQpolyDeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (pbwPolynomial (K := K) d) = (n : WithBot ℤ) := by rw [← hQsymbol, hQdeg]
  have hproductExpansion :
      (pbwProductCoeff (K := K) c d).sum
          (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        ((P * Q : A1 K) : Module.End K K[X]) := by
    calc
      _ = pbwOperatorLinear (K := K) (pbwProductCoeff c d) :=
        (pbwOperatorLinear_eq_sum (pbwProductCoeff c d)).symm
      _ = pbwOperatorLinear c * pbwOperatorLinear d := pbwProductCoeff_operator c d
      _ = (P : Module.End K K[X]) * (Q : Module.End K K[X]) := by
        rw [pbwOperatorLinear_eq_sum c, pbwOperatorLinear_eq_sum d, hPexp, hQexp]
      _ = _ := rfl
  have hprodSymbol := symbol_eq_pbwPolynomial_of_expansion (P * Q : A1 K)
    (pbwProductCoeff c d) hproductExpansion
  have hpbwPoly : pbwProductPoly (K := K) c d =
      pbwPolynomial (K := K) (pbwProductCoeff c d) := by
    rw [pbwProductPoly_eq_polynomialLinear, pbwPolynomialLinear_eq_pbwPolynomial]
  rw [hprodSymbol, ← hpbwPoly, hPsymbol, hQsymbol]
  exact pbwProductPoly_top ρ σ m n c d hpos hc hd hPpolyDeg hQpolyDeg

private theorem weightedTotalDegree'_sum_le (w : Fin 2 → ℤ) {α : Type*}
    (s : Finset α) (f : α → MvPolynomial (Fin 2) K) (N : ℤ)
    (h : ∀ i ∈ s, ∀ e ∈ (f i).support, Finsupp.weight w e ≤ N) :
    MvPolynomial.weightedTotalDegree' w (∑ i ∈ s, f i) ≤ (N : WithBot ℤ) := by
  classical
  rw [MvPolynomial.weightedTotalDegree', Finset.sup_le_iff]
  intro e he
  have he' := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he'
  rcases he' with ⟨i, hi, hie⟩
  exact WithBot.coe_le_coe.mpr (h i hi e hie)

private theorem weightedTotalDegree'_sub_le (w : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) K) (N : ℤ)
    (hp : MvPolynomial.weightedTotalDegree' w p ≤ (N : WithBot ℤ))
    (hq : MvPolynomial.weightedTotalDegree' w q ≤ (N : WithBot ℤ)) :
    MvPolynomial.weightedTotalDegree' w (p-q) ≤ (N : WithBot ℤ) := by
  classical
  rw [MvPolynomial.weightedTotalDegree', Finset.sup_le_iff]
  intro e he
  have he' : e ∈ p.support ∨ e ∈ q.support := by
    have hcoeff := MvPolynomial.mem_support_iff.mp he
    change MvPolynomial.coeff e p - MvPolynomial.coeff e q ≠ 0 at hcoeff
    by_cases hp0 : MvPolynomial.coeff e p = 0
    · right
      apply MvPolynomial.mem_support_iff.mpr
      intro hq0
      simp [hp0, hq0] at hcoeff
    · left
      exact MvPolynomial.mem_support_iff.mpr hp0
  rcases he' with hep | heq
  · have hle : (Finsupp.weight w e : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' w p := by
      change (Finsupp.weight w e : WithBot ℤ) ≤
        p.support.sup (fun d => (Finsupp.weight w d : WithBot ℤ))
      exact Finset.le_sup (f := fun d : Fin 2 →₀ ℕ =>
        (Finsupp.weight w d : WithBot ℤ)) hep
    exact hle.trans hp
  · have hle : (Finsupp.weight w e : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' w q := by
      change (Finsupp.weight w e : WithBot ℤ) ≤
        q.support.sup (fun d => (Finsupp.weight w d : WithBot ℤ))
      exact Finset.le_sup (f := fun d : Fin 2 →₀ ℕ =>
        (Finsupp.weight w d : WithBot ℤ)) heq
    exact hle.trans hq

private theorem pbwCorrectionPoly_degree_le (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (pbwCorrectionPoly (K := K) c d) ≤
      (m+n-(ρ+σ) : WithBot ℤ) := by
  classical
  apply weightedTotalDegree'_sum_le
  intro p hp e he
  have he₁ := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he₁
  rcases he₁ with ⟨q, hq, he₂⟩
  have he₂' := MvPolynomial.support_sum he₂
  simp only [Finset.mem_biUnion] at he₂'
  rcases he₂' with ⟨k, hk, he₃⟩
  have hcoeff : MvPolynomial.coeff e
      (MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he₃
  have hexp : e = expo (p.1 + q.1 - k) (p.2 + q.2 - k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  subst e
  have hkmem := Finset.mem_filter.mp hk
  have hkmin : k ≤ min q.1 p.2 := Nat.lt_succ_iff.mp (mem_range.mp hkmem.1)
  have hkpos : 0 < k := hkmem.2
  have hweight := normalOrdered_contraction_weight ρ σ p.1 p.2 q.1 q.2 k hkmin
  have hbase : Finsupp.weight (wt ρ σ) (expo (p.1+q.1) (p.2+q.2)) ≤ m+n := by
    rw [expo_add, map_add]
    exact add_le_add (hc p hp) (hd q hq)
  have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkpos
  have hmult : ρ+σ ≤ (k : ℤ)*(ρ+σ) := by
    simpa using mul_le_mul_of_nonneg_right hkz (le_of_lt hpos)
  omega

private theorem pbwProductPoly_commutator_eq_corrections
    (c d : (ℕ × ℕ) →₀ K) :
    pbwProductPoly (K := K) c d - pbwProductPoly (K := K) d c =
      pbwCorrectionPoly (K := K) c d - pbwCorrectionPoly (K := K) d c := by
  rw [pbwProductPoly_split, pbwProductPoly_split,
    uncontractedPoly_eq_mul, uncontractedPoly_eq_mul]
  ring

private theorem pbwProductPoly_commutator_degree_le (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (pbwProductPoly (K := K) c d - pbwProductPoly (K := K) d c) ≤
        (m+n-(ρ+σ) : WithBot ℤ) := by
  rw [pbwProductPoly_commutator_eq_corrections]
  apply weightedTotalDegree'_sub_le
  · exact pbwCorrectionPoly_degree_le ρ σ m n c d hpos hc hd
  · simpa only [add_comm n m] using
      (pbwCorrectionPoly_degree_le ρ σ n m d c hpos hd hc)

private theorem pbwProductPoly_degree_le (ρ σ m n : ℤ)
    (c d : (ℕ × ℕ) →₀ K)
    (hpos : 0 < ρ + σ)
    (hc : ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m)
    (hd : ∀ q ∈ d.support, Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (pbwProductPoly (K := K) c d) ≤
      (m + n : WithBot ℤ) := by
  classical
  apply weightedTotalDegree'_sum_le
  intro p hp e he
  have he₁ := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he₁
  rcases he₁ with ⟨q, hq, he₂⟩
  have he₂' := MvPolynomial.support_sum he₂
  simp only [Finset.mem_biUnion] at he₂'
  rcases he₂' with ⟨k, hk, he₃⟩
  have hcoeff : MvPolynomial.coeff e
      (MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he₃
  have hexp : e = expo (p.1 + q.1 - k) (p.2 + q.2 - k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  subst e
  have hkmin : k ≤ min q.1 p.2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  by_cases hkpos : 0 < k
  · have hdrop := normalOrdered_contraction_weight_lt ρ σ hpos
      p.1 p.2 q.1 q.2 k hkmin hkpos
    have hbase : Finsupp.weight (wt ρ σ) (expo (p.1 + q.1) (p.2 + q.2)) ≤ m + n := by
      rw [expo_add, map_add]
      exact add_le_add (hc p hp) (hd q hq)
    exact le_of_lt (lt_of_lt_of_le hdrop hbase)
  · have hkzero : k = 0 := Nat.eq_zero_of_not_pos hkpos
    subst k
    have hbase : Finsupp.weight (wt ρ σ) (expo (p.1 + q.1) (p.2 + q.2)) ≤ m + n := by
      rw [expo_add, map_add]
      exact add_le_add (hc p hp) (hd q hq)
    simpa using hbase

private theorem symbol_mul_weightedDegree_le [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ)) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol ((P * Q : A1 K) : Module.End K K[X])) ≤ (m+n : WithBot ℤ) := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hPsymbol : symbol (P : Module.End K K[X]) = pbwPolynomial (K := K) c :=
    symbol_eq_pbwPolynomial_of_expansion P c hPexp
  have hQsymbol : symbol (Q : Module.End K K[X]) = pbwPolynomial (K := K) d :=
    symbol_eq_pbwPolynomial_of_expansion Q d hQexp
  have hc : ∀ p ∈ c.support,
      Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m := by
    intro p hp
    have hmem : expo p.1 p.2 ∈ (symbol (P : Module.End K K[X])).support := by
      rw [hPsupport]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hle : (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol (P : Module.End K K[X])) := by
      change (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
        ((symbol (P : Module.End K K[X])).support).sup
          (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
      exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hmem
    rw [hPdeg] at hle
    exact WithBot.coe_le_coe.mp hle
  have hd : ∀ q ∈ d.support,
      Finsupp.weight (wt ρ σ) (expo q.1 q.2) ≤ n := by
    intro q hq
    have hmem : expo q.1 q.2 ∈ (symbol (Q : Module.End K K[X])).support := by
      rw [hQsupport]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hle : (Finsupp.weight (wt ρ σ) (expo q.1 q.2) : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol (Q : Module.End K K[X])) := by
      change (Finsupp.weight (wt ρ σ) (expo q.1 q.2) : WithBot ℤ) ≤
        ((symbol (Q : Module.End K K[X])).support).sup
          (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
      exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hmem
    rw [hQdeg] at hle
    exact WithBot.coe_le_coe.mp hle
  have hproductExpansion :
      (pbwProductCoeff (K := K) c d).sum
          (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        ((P * Q : A1 K) : Module.End K K[X]) := by
    calc
      _ = pbwOperatorLinear (K := K) (pbwProductCoeff c d) :=
        (pbwOperatorLinear_eq_sum (pbwProductCoeff c d)).symm
      _ = pbwOperatorLinear c * pbwOperatorLinear d := pbwProductCoeff_operator c d
      _ = (P : Module.End K K[X]) * (Q : Module.End K K[X]) := by
        rw [pbwOperatorLinear_eq_sum c, pbwOperatorLinear_eq_sum d, hPexp, hQexp]
      _ = _ := rfl
  have hprodSymbol := symbol_eq_pbwPolynomial_of_expansion (P * Q : A1 K)
    (pbwProductCoeff c d) hproductExpansion
  have hpbwPoly : pbwProductPoly (K := K) c d =
      pbwPolynomial (K := K) (pbwProductCoeff c d) := by
    rw [pbwProductPoly_eq_polynomialLinear, pbwPolynomialLinear_eq_pbwPolynomial]
  rw [hprodSymbol, ← hpbwPoly]
  simpa using pbwProductPoly_degree_le ρ σ m n c d hpos hc hd

theorem weightedComponent_ne_zero_of_weightedTotalDegree_eq
    (w : Fin 2 → ℤ) (p : MvPolynomial (Fin 2) K) (m : ℤ)
    (hdeg : MvPolynomial.weightedTotalDegree' w p = (m : WithBot ℤ)) :
    MvPolynomial.weightedHomogeneousComponent w m p ≠ 0 := by
  classical
  have hsupp : p.support.Nonempty := by
    by_contra h
    have hzero : p.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [MvPolynomial.weightedTotalDegree', hzero] at hdeg
  obtain ⟨d, hd, hmax⟩ := Finset.sup_mem_of_nonempty
    (s := p.support) (f := fun e => (Finsupp.weight w e : WithBot ℤ)) hsupp
  have hdweight : Finsupp.weight w d = m := by
    have hEq : (Finsupp.weight w d : WithBot ℤ) =
        MvPolynomial.weightedTotalDegree' w p := hmax
    rw [hdeg] at hEq
    exact WithBot.coe_eq_coe.mp hEq
  intro hcomp
  have hc := congrArg (MvPolynomial.coeff d) hcomp
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hdweight] at hc
  have hcoeff : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  exact hcoeff hc

theorem weightedComponent_ne_zero_degree_lower_bound
    (w : Fin 2 → ℤ) (p : MvPolynomial (Fin 2) K) (m : ℤ)
    (hcomp : MvPolynomial.weightedHomogeneousComponent w m p ≠ 0) :
    (m : WithBot ℤ) ≤ MvPolynomial.weightedTotalDegree' w p := by
  classical
  obtain ⟨d, hdCoeff⟩ := MvPolynomial.ne_zero_iff.mp hcomp
  have hd : d ∈ (MvPolynomial.weightedHomogeneousComponent w m p).support :=
    MvPolynomial.mem_support_iff.mpr hdCoeff
  rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
  rcases Finset.mem_filter.mp hd with ⟨hdp, hdweight⟩
  have hle : (Finsupp.weight w d : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' w p := by
    change (Finsupp.weight w d : WithBot ℤ) ≤
      p.support.sup (fun e => (Finsupp.weight w e : WithBot ℤ))
    exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
      (Finsupp.weight w e : WithBot ℤ)) hdp
  rw [hdweight] at hle
  exact hle

/-- For a positive-total-weight direction, the top weighted degree of a Weyl product is the sum
of the degrees, and its leading form is the product of the leading forms. -/
theorem symbol_mul_degree_and_leadingForm [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ)) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol ((P * Q : A1 K) : Module.End K K[X])) = (m+n : WithBot ℤ) ∧
      leadingForm ρ σ ((P * Q : A1 K) : Module.End K K[X]) =
        leadingForm ρ σ (P : Module.End K K[X]) *
          leadingForm ρ σ (Q : Module.End K K[X]) := by
  have hupper := symbol_mul_weightedDegree_le P Q ρ σ m n hpos hPdeg hQdeg
  have hPtop := weightedComponent_ne_zero_of_weightedTotalDegree_eq (wt ρ σ)
    (symbol (P : Module.End K K[X])) m hPdeg
  have hQtop := weightedComponent_ne_zero_of_weightedTotalDegree_eq (wt ρ σ)
    (symbol (Q : Module.End K K[X])) n hQdeg
  have hproductTop : MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m+n)
      (symbol ((P * Q : A1 K) : Module.End K K[X])) ≠ 0 := by
    rw [symbol_mul_top_component P Q ρ σ m n hpos hPdeg hQdeg]
    exact mul_ne_zero hPtop hQtop
  have hlower := weightedComponent_ne_zero_degree_lower_bound (wt ρ σ)
    (symbol ((P * Q : A1 K) : Module.End K K[X])) (m+n) hproductTop
  have hdegree : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol ((P * Q : A1 K) : Module.End K K[X])) = (m+n : WithBot ℤ) :=
    le_antisymm hupper (by simpa using hlower)
  have hvP : vDeg ρ σ (P : Module.End K K[X]) = m := by simp [vDeg, hPdeg]
  have hvQ : vDeg ρ σ (Q : Module.End K K[X]) = n := by simp [vDeg, hQdeg]
  have hvPQ : vDeg ρ σ ((P * Q : A1 K) : Module.End K K[X]) = m+n := by
    change WithBot.unbotD 0
      (MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol ((P * Q : A1 K) : Module.End K K[X]))) = m+n
    rw [hdegree]
    rfl
  constructor
  · exact hdegree
  · simp only [leadingForm, hvP, hvQ, hvPQ]
    exact symbol_mul_top_component P Q ρ σ m n hpos hPdeg hQdeg

private theorem pbwCoefficient_weight_le_of_symbol_deg [CharZero K]
    (T : A1 K) (c : (ℕ × ℕ) →₀ K) (ρ σ m : ℤ)
    (hsupport : (symbol (T : Module.End K K[X])).support =
      c.support.image (fun p => expo p.1 p.2))
    (hdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (T : Module.End K K[X])) = (m : WithBot ℤ)) :
    ∀ p ∈ c.support, Finsupp.weight (wt ρ σ) (expo p.1 p.2) ≤ m := by
  intro p hp
  have hmem : expo p.1 p.2 ∈ (symbol (T : Module.End K K[X])).support := by
    rw [hsupport]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hle : (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol (T : Module.End K K[X])) := by
    change (Finsupp.weight (wt ρ σ) (expo p.1 p.2) : WithBot ℤ) ≤
      ((symbol (T : Module.End K K[X])).support).sup
        (fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
    exact Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
      (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hmem
  rw [hdeg] at hle
  exact WithBot.coe_le_coe.mp hle

/-- At the first possible commutator weight, the symbol of the exact Weyl commutator has the
Poisson bracket of the two leading forms as its component. -/
theorem symbol_commutator_top_component [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ)) :
    MvPolynomial.weightedHomogeneousComponent (wt ρ σ) (m+n-(ρ+σ))
      (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X])) =
    poisson (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m
      (symbol (P : Module.End K K[X])))
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) n
        (symbol (Q : Module.End K K[X]))) := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hPsymbol : symbol (P : Module.End K K[X]) = pbwPolynomial (K := K) c :=
    symbol_eq_pbwPolynomial_of_expansion P c hPexp
  have hQsymbol : symbol (Q : Module.End K K[X]) = pbwPolynomial (K := K) d :=
    symbol_eq_pbwPolynomial_of_expansion Q d hQexp
  have hc := pbwCoefficient_weight_le_of_symbol_deg P c ρ σ m hPsupport hPdeg
  have hd := pbwCoefficient_weight_le_of_symbol_deg Q d ρ σ n hQsupport hQdeg
  rw [symbol_sub, symbol_mul_eq_pbwProductPoly_of_expansions P Q c d hPexp hQexp,
    symbol_mul_eq_pbwProductPoly_of_expansions Q P d c hQexp hPexp,
    hPsymbol, hQsymbol]
  exact pbwProductPoly_commutator_top ρ σ m n c d hpos hc hd

private theorem symbol_commutator_weightedDegree_le [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ)) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X])) ≤
        (m+n-(ρ+σ) : WithBot ℤ) := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hc := pbwCoefficient_weight_le_of_symbol_deg P c ρ σ m hPsupport hPdeg
  have hd := pbwCoefficient_weight_le_of_symbol_deg Q d ρ σ n hQsupport hQdeg
  rw [symbol_sub, symbol_mul_eq_pbwProductPoly_of_expansions P Q c d hPexp hQexp,
    symbol_mul_eq_pbwProductPoly_of_expansions Q P d c hQexp hPexp]
  exact pbwProductPoly_commutator_degree_le ρ σ m n c d hpos hc hd

/-- When the Poisson bracket of two weighted leading forms is nonzero, it is exactly the
leading form of their Weyl commutator, at the predicted weight. -/
theorem symbol_commutator_degree_and_leadingForm [CharZero K]
    (P Q : A1 K) (ρ σ m n : ℤ) (hpos : 0 < ρ + σ)
    (hPdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (n : WithBot ℤ))
    (hbracket : poisson
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m
        (symbol (P : Module.End K K[X])))
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) n
        (symbol (Q : Module.End K K[X]))) ≠ 0) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X])) =
        (m+n-(ρ+σ) : WithBot ℤ) ∧
    leadingForm ρ σ ((P*Q-Q*P : A1 K) : Module.End K K[X]) =
      poisson (leadingForm ρ σ (P : Module.End K K[X]))
        (leadingForm ρ σ (Q : Module.End K K[X])) := by
  have hupper := symbol_commutator_weightedDegree_le P Q ρ σ m n hpos hPdeg hQdeg
  have htop := symbol_commutator_top_component P Q ρ σ m n hpos hPdeg hQdeg
  have hnonzero : MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
      (m+n-(ρ+σ))
      (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X])) ≠ 0 := by
    rw [htop]
    exact hbracket
  have hlower := weightedComponent_ne_zero_degree_lower_bound (wt ρ σ)
    (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X]))
    (m+n-(ρ+σ)) hnonzero
  have hdegree : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X])) =
        (m+n-(ρ+σ) : WithBot ℤ) := le_antisymm hupper hlower
  have hvP : vDeg ρ σ (P : Module.End K K[X]) = m := by simp [vDeg, hPdeg]
  have hvQ : vDeg ρ σ (Q : Module.End K K[X]) = n := by simp [vDeg, hQdeg]
  have hvComm : vDeg ρ σ ((P*Q-Q*P : A1 K) : Module.End K K[X]) =
      m+n-(ρ+σ) := by
    change WithBot.unbotD 0
      (MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol ((P*Q-Q*P : A1 K) : Module.End K K[X]))) = m+n-(ρ+σ)
    rw [hdegree]
    rfl
  constructor
  · exact hdegree
  · simp only [leadingForm, hvP, hvQ, hvComm]
    exact htop

private theorem weightedDegree_eq_vDeg_of_leadingForm_ne_zero [CharZero K]
    (T : A1 K) (ρ σ : ℤ)
    (h : leadingForm ρ σ (T : Module.End K K[X]) ≠ 0) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (T : Module.End K K[X])) =
        (vDeg ρ σ (T : Module.End K K[X]) : WithBot ℤ) := by
  have hsymbol : symbol (T : Module.End K K[X]) ≠ 0 := by
    intro hz
    apply h
    simp [leadingForm, hz]
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ)
      (symbol (T : Module.End K K[X])) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  rw [← hm]
  simp [vDeg, ← hm]

/-- The paper-facing commutator law. Its nonzero Poisson hypothesis itself guarantees that
both operand weighted degrees are genuine, so no separate nonzero hypotheses are needed. -/
theorem leadingForm_commutator [CharZero K]
    (P Q : A1 K) (ρ σ : ℤ) (hweight : 0 < ρ + σ)
    (h : poisson (leadingForm ρ σ (Q : Module.End K K[X]))
      (leadingForm ρ σ (P : Module.End K K[X])) ≠ 0) :
    vDeg ρ σ ((Q*P-P*Q : A1 K) : Module.End K K[X]) =
      vDeg ρ σ (Q : Module.End K K[X]) +
        vDeg ρ σ (P : Module.End K K[X]) - (ρ+σ) ∧
    leadingForm ρ σ ((Q*P-P*Q : A1 K) : Module.End K K[X]) =
      poisson (leadingForm ρ σ (Q : Module.End K K[X]))
        (leadingForm ρ σ (P : Module.End K K[X])) := by
  have hQform : leadingForm ρ σ (Q : Module.End K K[X]) ≠ 0 := by
    intro hz
    apply h
    simp [hz, poisson]
  have hPform : leadingForm ρ σ (P : Module.End K K[X]) ≠ 0 := by
    intro hz
    apply h
    simp [hz, poisson]
  have hQdeg := weightedDegree_eq_vDeg_of_leadingForm_ne_zero Q ρ σ hQform
  have hPdeg := weightedDegree_eq_vDeg_of_leadingForm_ne_zero P ρ σ hPform
  have hcore := symbol_commutator_degree_and_leadingForm Q P ρ σ
    (vDeg ρ σ (Q : Module.End K K[X]))
    (vDeg ρ σ (P : Module.End K K[X])) hweight hQdeg hPdeg (by
      simpa only [leadingForm] using h)
  constructor
  · change WithBot.unbotD 0
      (MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol ((Q*P-P*Q : A1 K) : Module.End K K[X]))) = _
    rw [hcore.1]
    rfl
  · exact hcore.2

theorem mass_eq_pbwExpansionGradeSupport [CharZero K]
    (T : A1 K) :
    ∃ c : (ℕ × ℕ) →₀ K,
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
        (T : Module.End K K[X]) ∧
      mass (T : Module.End K K[X]) =
        (c.support.image (fun p => (p.1 : ℤ) - (p.2 : ℤ))).card := by
  classical
  obtain ⟨c, hc, hsup⟩ := symbol_support_eq_pbwCoefficientImage T
  have hgrade : (fun p : ℕ × ℕ => grade (expo p.1 p.2)) =
      (fun p => (p.1 : ℤ) - (p.2 : ℤ)) := by
    funext p
    rcases p with ⟨i,j⟩
    simp [grade, expo]
  refine ⟨c, hc, ?_⟩
  unfold mass
  rw [hsup, Finset.image_image]
  have hcomp : grade ∘ (fun p : ℕ × ℕ => expo p.1 p.2) =
      (fun p => (p.1 : ℤ) - (p.2 : ℤ)) := by
    funext p
    exact congrFun hgrade p
  rw [hcomp]

/-- The PBW symbol distinguishes elements of the concrete Weyl operator algebra. -/
theorem symbol_injective [CharZero K]
    {P Q : A1 K}
    (h : symbol (P : Module.End K K[X]) = symbol (Q : Module.End K K[X])) : P = Q := by
  apply Subtype.ext
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion P
  obtain ⟨d, hd⟩ := A1_exists_finiteNormalOrderedExpansion Q
  have hcd : c = d := by
    ext p
    have hp : c p = pbwCoeff (P : Module.End K K[X]) p.1 p.2 := by
      symm
      rw [← hc]
      exact pbwCoeff_finsuppNormalOrderedSum c p.1 p.2
    have hq : d p = pbwCoeff (Q : Module.End K K[X]) p.1 p.2 := by
      symm
      rw [← hd]
      exact pbwCoeff_finsuppNormalOrderedSum d p.1 p.2
    rw [hp, hq]
    have hcoeff := congrArg (MvPolynomial.coeff (expo p.1 p.2)) h
    rw [symbol_coeff_pbwCoeff, symbol_coeff_pbwCoeff] at hcoeff
    exact hcoeff
  calc
    P.1 = c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) := hc.symm
    _ = d.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) := by rw [hcd]
    _ = Q.1 := hd

theorem xOp_mem_A1 : xOp K ∈ A1 K := Algebra.subset_adjoin (by simp)

theorem yOp_mem_A1 : yOp K ∈ A1 K := Algebra.subset_adjoin (by simp)

/-- The generators of `A1 K` satisfy `[Y, X] = 1`. -/
theorem generators_commutator :
    (⟨yOp K, yOp_mem_A1⟩ : A1 K) * ⟨xOp K, xOp_mem_A1⟩ - ⟨xOp K, xOp_mem_A1⟩ * ⟨yOp K, yOp_mem_A1⟩
      = 1 := by
  apply Subtype.ext
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
  exact yOp_mul_xOp_sub_xOp_mul_yOp

theorem sum_neg_one_pow_choose (j : ℕ) :
    ∑ k ∈ range (j + 1), (-1 : K) ^ (j - k) * (j.choose k : K) = if j = 0 then 1 else 0 := by
  have h := add_pow (1 : K) (-1) j
  simp only [one_pow, one_mul, add_neg_cancel] at h
  rw [← h]
  rcases j with _ | j <;> simp

theorem coeffPoly_xOp (j : ℕ) : coeffPoly (xOp K) j = if j = 0 then X else 0 := by
  unfold coeffPoly xOp
  have hterm : ∀ k ∈ range (j + 1), C ((-1 : K) ^ (j - k) * (j.choose k : K)) * X ^ (j - k) *
      (LinearMap.mulLeft K (X : K[X])) (X ^ k)
        = C ((-1 : K) ^ (j - k) * (j.choose k : K)) * X ^ (j + 1) := by
    intro k hk
    rw [mem_range] at hk
    rw [LinearMap.mulLeft_apply, mul_assoc, ← pow_succ', ← pow_add]
    congr 2
    omega
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, sum_neg_one_pow_choose]
  split_ifs with hj
  · subst hj; simp
  · simp

theorem pbwCoeff_xOp (i j : ℕ) : pbwCoeff (xOp K) i j = if i = 1 ∧ j = 0 then 1 else 0 := by
  unfold pbwCoeff
  rw [coeffPoly_xOp]
  split_ifs with hj h1 h1 <;> simp_all [coeff_X]
  omega

/-- The PBW symbol of multiplication by `X` is `x`. -/
theorem symbol_xOp : symbol (xOp K) = MvPolynomial.X 0 := by
  unfold symbol
  rw [finsum_eq_single _ (1, 0)]
  · simp [pbwCoeff_xOp, expo, MvPolynomial.X]
  · rintro ⟨i, j⟩ hne
    rw [pbwCoeff_xOp, if_neg, map_zero]
    rintro ⟨rfl, rfl⟩
    exact hne rfl

/-- Multiplication by `X` has mass one. -/
theorem mass_xOp : mass (xOp K) = 1 := by
  unfold mass
  rw [symbol_xOp, MvPolynomial.support_X]
  simp

/-- Exact PBW contractions bound both output coordinates by the sums of source coordinates. -/
 theorem symbol_mul_coordinate_bounds [CharZero K] (P Q : A1 K)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (symbol ((P*Q : A1 K).val)).support) :
    ∃ d ∈ (symbol P.val).support, ∃ f ∈ (symbol Q.val).support,
      e 0 ≤ d 0+f 0 ∧ e 1 ≤ d 1+f 1 := by
  classical
  obtain ⟨c, hPexp, hPsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  obtain ⟨d, hQexp, hQsupport⟩ := symbol_support_eq_pbwCoefficientImage Q
  have hprod := symbol_mul_eq_pbwProductPoly_of_expansions P Q c d hPexp hQexp
  rw [hprod] at he
  unfold pbwProductPoly at he
  have hpqk := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at hpqk
  rcases hpqk with ⟨p, hp, hpqk⟩
  have hqk := MvPolynomial.support_sum hpqk
  simp only [Finset.mem_biUnion] at hqk
  rcases hqk with ⟨q, hq, hk⟩
  have hk' := MvPolynomial.support_sum hk
  simp only [Finset.mem_biUnion] at hk'
  rcases hk' with ⟨k, hk, hmono⟩
  have hcoef : MvPolynomial.coeff e
      (MvPolynomial.monomial (expo (p.1 + q.1 - k) (p.2 + q.2 - k))
        (c p * d q * (p.2.choose k * q.1.descFactorial k : K))) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmono
  have heq : e = expo (p.1 + q.1 - k) (p.2 + q.2 - k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoef
    exact hcoef rfl
  refine ⟨expo p.1 p.2, ?_, expo q.1 q.2, ?_, ?_⟩
  · rw [hPsupport]
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · rw [hQsupport]
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
  · rw [heq]
    simp only [expo,Finsupp.add_apply,Finsupp.single_apply]
    norm_num


end Dixmier.Weyl
