/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Moments
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.LinearCombination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Repeated roots of sparse polynomials

* `rootMultiplicity_lt_termCount`: a nonzero root of a polynomial with `t` terms has
  multiplicity at most `t - 1`;
* `eq_one_of_forall_pow_eq_one`: primitive exponent support makes the support root-of-unity
  rigid;
* `eq_of_five_terms`: two nonzero roots of multiplicity at least four of a five-term polynomial
  with rigid support coincide;
* `exists_affine_of_moments`: a weight vector on six exponents annihilating all cubic test
  polynomials is, after multiplication by the real node products, affine in the exponent.
-/

namespace Dixmier

open Polynomial Finset

section Field

variable {K : Type*} [Field K]

/-- A sum against a test polynomial vanishing off `U` reduces to a sum over `U`. -/
theorem sum_testPoly_sdiff {N U : Finset ℕ} (hU : U ⊆ N) (w : ℕ → K) :
    ∑ m ∈ N, w m * (testPoly (N \ U) : K[X]).eval (m : K)
      = ∑ m ∈ U, w m * (testPoly (N \ U) : K[X]).eval (m : K) := by
  symm
  refine Finset.sum_subset hU fun m hmN hmU => ?_
  rw [eval_testPoly_eq_zero (mem_sdiff.mpr ⟨hmN, hmU⟩), mul_zero]

/-- Splitting a node product at a subset containing the node. -/
theorem prod_erase_eq_eval_testPoly_mul {N U : Finset ℕ} (hU : U ⊆ N) {k : ℕ} (hk : k ∈ U) :
    ∏ m ∈ N.erase k, ((k : K) - m)
      = (testPoly (N \ U) : K[X]).eval (k : K) * ∏ m ∈ U.erase k, ((k : K) - m) := by
  rw [eval_testPoly, ← Finset.prod_union]
  · congr 1
    ext m
    simp only [mem_erase, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hmk, hmN⟩
      by_cases hmU : m ∈ U
      · exact Or.inr ⟨hmk, hmU⟩
      · exact Or.inl ⟨hmN, hmU⟩
    · rintro (⟨hmN, hmU⟩ | ⟨hmk, hmU⟩)
      · exact ⟨fun h => hmU (h ▸ hk), hmN⟩
      · exact ⟨hmk, hU hmU⟩
  · rw [Finset.disjoint_left]
    intro m hm hm'
    exact (mem_sdiff.mp hm).2 (mem_of_mem_erase hm')

variable [CharZero K]

/-- Sparse multiplicity bound: if `(X - a)^m ∣ S` with `S ≠ 0` and `a ≠ 0`, then `m` is less
than the number of terms of `S`. -/
theorem pow_dvd_imp_lt_termCount {S : K[X]} (hS : S ≠ 0) {a : K} (ha : a ≠ 0) {m : ℕ}
    (hdvd : (X - C a) ^ m ∣ S) : m < termCount S := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨n₀, hn₀⟩ : S.support.Nonempty := Polynomial.support_nonempty.mpr hS
  have hdvd' : (X - C a) ^ termCount S ∣ S := (pow_dvd_pow _ hcon).trans hdvd
  have hg : (testPoly (S.support.erase n₀) : K[X]).natDegree < termCount S := by
    refine (natDegree_testPoly_le _).trans_lt ?_
    rw [card_erase_of_mem hn₀]
    unfold termCount
    exact Nat.sub_lt (card_pos.mpr ⟨n₀, hn₀⟩) one_pos
  have hmom := moment_eq_zero hdvd' hg
  rw [Finset.sum_eq_single n₀
    (fun n hn hne => by rw [eval_testPoly_eq_zero (mem_erase.mpr ⟨hne, hn⟩), mul_zero])
    (fun h => absurd hn₀ h)] at hmom
  have h1 : S.coeff n₀ ≠ 0 := mem_support_iff.mp hn₀
  have h2 : (testPoly (S.support.erase n₀) : K[X]).eval (n₀ : K) ≠ 0 :=
    eval_testPoly_ne_zero (notMem_erase n₀ _)
  exact mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ ha)) h2 hmom

/-- Sparse multiplicity bound in terms of `rootMultiplicity`. -/
theorem rootMultiplicity_lt_termCount {S : K[X]} (hS : S ≠ 0) {a : K} (ha : a ≠ 0) :
    rootMultiplicity a S < termCount S :=
  pow_dvd_imp_lt_termCount hS ha (pow_rootMultiplicity_dvd S a)

end Field

/-- Primitive exponent support is root-of-unity rigid. -/
theorem eq_one_of_forall_pow_eq_one {R M : Type*} [Semiring R] [Monoid M] {S : R[X]}
    (h : HasPrimitiveSupport S) {ζ : M} (hζ : ∀ n ∈ S.support, ζ ^ n = 1) : ζ = 1 := by
  have hdvd : orderOf ζ ∣ (S.support.erase 0).gcd id :=
    Finset.dvd_gcd fun n hn => orderOf_dvd_of_pow_eq_one (hζ n (mem_of_mem_erase hn))
  rw [h.2, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.mp hdvd

section Rigid

variable {K : Type*} [Field K] [CharZero K]

/-- Two nonzero roots of multiplicity at least four of a five-term polynomial with nonzero
constant coefficient and root-of-unity rigid support coincide. -/
theorem eq_of_five_terms {S : K[X]} (h5 : termCount S = 5) (h0 : S.coeff 0 ≠ 0)
    (hrig : ∀ ζ : K, (∀ n ∈ S.support, ζ ^ n = 1) → ζ = 1) {α β : K} (hβ : β ≠ 0)
    (hα4 : (X - C α) ^ 4 ∣ S) (hβ4 : (X - C β) ^ 4 ∣ S) : α = β := by
  have h0s : (0 : ℕ) ∈ S.support := mem_support_iff.mpr h0
  have key : ∀ n ∈ S.support, α ^ n = β ^ n := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    set U : Finset ℕ := {0, n} with hUdef
    have hU : U ⊆ S.support := by
      intro m hm; simp only [hUdef, mem_insert, mem_singleton] at hm
      rcases hm with rfl | rfl; exacts [h0s, hn]
    have hcard : (S.support \ U).card = 3 := by
      rw [card_sdiff_of_subset hU, card_pair (Ne.symm hn0)]; unfold termCount at h5; omega
    have hg : (testPoly (S.support \ U) : K[X]).natDegree < 4 :=
      (natDegree_testPoly_le _).trans_lt (by omega)
    have hne : (testPoly (S.support \ U) : K[X]).eval (n : K) ≠ 0 :=
      eval_testPoly_ne_zero fun h => (mem_sdiff.mp h).2 (by simp [hUdef])
    have hred : ∀ a : K, ∑ m ∈ S.support, S.coeff m * a ^ m *
        (testPoly (S.support \ U) : K[X]).eval (m : K)
        = S.coeff 0 * (testPoly (S.support \ U) : K[X]).eval ((0 : ℕ) : K)
          + S.coeff n * a ^ n * (testPoly (S.support \ U) : K[X]).eval (n : K) := by
      intro a
      rw [sum_testPoly_sdiff hU (fun m => S.coeff m * a ^ m), hUdef,
        Finset.sum_pair (Ne.symm hn0), pow_zero, mul_one]
    have hmα := moment_eq_zero hα4 hg
    have hmβ := moment_eq_zero hβ4 hg
    rw [hred] at hmα hmβ
    have hSn : S.coeff n ≠ 0 := mem_support_iff.mp hn
    have hdiff : S.coeff n * (testPoly (S.support \ U) : K[X]).eval (n : K) * (α ^ n - β ^ n)
        = 0 := by linear_combination hmα - hmβ
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd h (mul_ne_zero hSn hne)
    · exact sub_eq_zero.mp h
  have hratio := hrig (α / β) fun n hn => by
    rw [div_pow, key n hn, div_self (pow_ne_zero _ hβ)]
  exact (div_eq_one_iff_eq hβ).mp hratio

end Rigid

end Dixmier
