/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.SparseRoots
public import DixmierFormal.Scalar.ExpQuadratic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Two fourth-order roots of a six-term polynomial

The four vanishing moments at a fourth-order root leave a two-dimensional kernel; every kernel
vector becomes affine in the exponent after multiplication by the real node products
(`exists_affine_of_moments`).  For two fourth-order roots `1` and `β`, the Rolle bound of
`ExpQuadratic` forces `|β| = 1`, and then primitivity forces the conjugation relation
`S_n βⁿ = conj S_n` (`normSq_eq_one_and_coeff_mul_pow_eq_conj`).
-/

namespace Dixmier

open Polynomial Finset ComplexConjugate

section Kernel

variable {K : Type*} [Field K] [CharZero K]

theorem sum_triple {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b c : ℕ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ∑ m ∈ ({a, b, c} : Finset ℕ), f m = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, add_assoc]

theorem erase_triple_fst {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) :
    ({a, b, c} : Finset ℕ).erase a = {b, c} := by
  ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega

theorem erase_triple_snd {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    ({a, b, c} : Finset ℕ).erase b = {a, c} := by
  ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega

theorem erase_triple_thd {a b c : ℕ} (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset ℕ).erase c = {a, b} := by
  ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega

/-- A weight vector on six exponents (containing `0`) that annihilates every test polynomial of
degree at most three is affine in the exponent after multiplication by the node products
`∏_{m ≠ n} (n - m)`. -/
theorem exists_affine_of_moments {N : Finset ℕ} (hN : N.card = 6) (h0 : 0 ∈ N) (w : ℕ → K)
    (hw : ∀ g : K[X], g.natDegree < 4 → ∑ m ∈ N, w m * g.eval (m : K) = 0) :
    ∃ A B : K, ∀ n ∈ N, w n * ∏ m ∈ N.erase n, ((n : K) - m) = A + B * n := by
  obtain ⟨n₁, hn₁, hn₁0⟩ := Finset.exists_mem_ne (by omega : 1 < N.card) 0
  have hn₁K : (n₁ : K) ≠ 0 := Nat.cast_ne_zero.mpr hn₁0
  set A : K := w 0 * ∏ m ∈ N.erase 0, (((0 : ℕ) : K) - m) with hA
  set B : K := (w n₁ * ∏ m ∈ N.erase n₁, ((n₁ : K) - m) - A) / n₁ with hB
  have hBn : B * n₁ = w n₁ * ∏ m ∈ N.erase n₁, ((n₁ : K) - m) - A := div_mul_cancel₀ _ hn₁K
  refine ⟨A, B, fun n hn => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [hA]
  rcases eq_or_ne n n₁ with rfl | hnn₁
  · linear_combination -hBn
  set U : Finset ℕ := {0, n₁, n} with hUdef
  have hUN : U ⊆ N := by
    intro m hm
    simp only [hUdef, mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> assumption
  have hUcard : U.card = 3 := by
    rw [hUdef, Finset.card_insert_of_notMem (by simp [Ne.symm hn₁0, Ne.symm hn0]),
      card_pair (Ne.symm hnn₁)]
  have hg : (testPoly (N \ U) : K[X]).natDegree < 4 :=
    (natDegree_testPoly_le _).trans_lt (by rw [card_sdiff_of_subset hUN]; omega)
  have hrel := hw _ hg
  rw [sum_testPoly_sdiff hUN w, hUdef, sum_triple _ (Ne.symm hn₁0) (Ne.symm hn0) (Ne.symm hnn₁)]
    at hrel
  have hD0 := prod_erase_eq_eval_testPoly_mul (K := K) hUN (show 0 ∈ U by simp [hUdef])
  have hD1 := prod_erase_eq_eval_testPoly_mul (K := K) hUN (show n₁ ∈ U by simp [hUdef])
  have hDn := prod_erase_eq_eval_testPoly_mul (K := K) hUN (show n ∈ U by simp [hUdef])
  rw [hUdef, erase_triple_fst (Ne.symm hn₁0) (Ne.symm hn0), prod_pair (Ne.symm hnn₁)] at hD0
  rw [hUdef, erase_triple_snd (Ne.symm hn₁0) (Ne.symm hnn₁), prod_pair (Ne.symm hn0)] at hD1
  rw [hUdef, erase_triple_thd (Ne.symm hn0) (Ne.symm hnn₁), prod_pair (Ne.symm hn₁0)] at hDn
  have key : (n₁ : K) * (w n * ∏ m ∈ N.erase n, ((n : K) - m))
      = (n₁ : K) * A + (w n₁ * ∏ m ∈ N.erase n₁, ((n₁ : K) - m) - A) * n := by
    rw [hA, hD0, hD1, hDn]
    push_cast at hrel ⊢
    linear_combination ((n₁ : K) * n * (n - n₁)) * hrel
  have h' : (n₁ : K) * (w n * ∏ m ∈ N.erase n, ((n : K) - m) - (A + B * n)) = 0 := by
    linear_combination key - (n : K) * hBn
  linear_combination (mul_eq_zero.mp h').resolve_left hn₁K

end Kernel

section Core

/-- Core of the two-root lemma: if `1` and `β ≠ 1` are roots of multiplicity at least four of a
six-term polynomial with constant coefficient one and rigid support, then `|β| = 1` and
`S_n βⁿ = conj S_n` for every `n`. -/
theorem normSq_eq_one_and_coeff_mul_pow_eq_conj {S : ℂ[X]} (h6 : termCount S = 6)
    (h1 : S.coeff 0 = 1) (hrig : ∀ ζ : ℂ, (∀ n ∈ S.support, ζ ^ n = 1) → ζ = 1)
    (hone : (X - C 1) ^ 4 ∣ S) {β : ℂ} (hβ4 : (X - C β) ^ 4 ∣ S) (hβ1 : β ≠ 1) :
    Complex.normSq β = 1 ∧ ∀ n, S.coeff n * β ^ n = conj (S.coeff n) := by
  have h0N : 0 ∈ S.support := mem_support_iff.mpr (by rw [h1]; exact one_ne_zero)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have hX : X ∣ S := by
      have := (dvd_pow_self (X - C (0 : ℂ)) (by norm_num : 4 ≠ 0)).trans hβ4
      simpa using this
    rw [X_dvd_iff, h1] at hX
    exact one_ne_zero hX
  have hN6 : S.support.card = 6 := h6
  set N := S.support with hN
  set D : ℕ → ℂ := fun n => ∏ m ∈ N.erase n, ((n : ℂ) - m) with hD
  have hDne : ∀ n ∈ N, D n ≠ 0 := by
    intro n _
    refine prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr ?_
    exact_mod_cast (ne_of_mem_erase hm).symm
  have hDconj : ∀ n, conj (D n) = D n := by intro n; simp [hD, map_prod]
  obtain ⟨A, B, hAB⟩ := exists_affine_of_moments (K := ℂ) hN6 h0N (fun m => S.coeff m)
    (fun g hg => by simpa using moment_eq_zero hone hg)
  obtain ⟨A', B', hAB'⟩ := exists_affine_of_moments (K := ℂ) hN6 h0N
    (fun m => S.coeff m * β ^ m) (fun g hg => moment_eq_zero hβ4 hg)
  have hA : A = D 0 := by
    have h := hAB 0 h0N
    simp only [h1, one_mul, Nat.cast_zero, mul_zero, add_zero] at h
    rw [← h]; simp only [hD, Nat.cast_zero]
  have hA' : A' = D 0 := by
    have h := hAB' 0 h0N
    simp only [h1, pow_zero, one_mul, mul_one, Nat.cast_zero, mul_zero, add_zero] at h
    rw [← h]; simp only [hD, Nat.cast_zero]
  set a : ℝ := (D 0).re with ha
  have haD : (a : ℂ) = D 0 := Complex.conj_eq_iff_re.mp (hDconj 0)
  have ha0 : a ≠ 0 := by
    intro h; apply hDne 0 h0N; rw [← haD, h, Complex.ofReal_zero]
  have hSD : ∀ n ∈ N, S.coeff n * D n = (a : ℂ) + B * n := by
    intro n hn; rw [haD, ← hA]; exact hAB n hn
  have hrel : ∀ n ∈ N, β ^ n * ((a : ℂ) + B * n) = (a : ℂ) + B' * n := by
    intro n hn
    rw [← hSD n hn, haD, ← hA']
    have h := hAB' n hn
    rw [← h]; ring
  have hsq : ∀ (z : ℂ) (n : ℕ), Complex.normSq ((a : ℂ) + z * n)
      = a ^ 2 + 2 * a * z.re * n + (z.re ^ 2 + z.im ^ 2) * (n : ℝ) ^ 2 := by
    intro z n; rw [Complex.normSq_apply]; simp; ring
  have hNR : ∀ n ∈ N, Complex.normSq β ^ n * (a ^ 2 + 2 * a * B.re * n
      + (B.re ^ 2 + B.im ^ 2) * (n : ℝ) ^ 2)
      = a ^ 2 + 2 * a * B'.re * n + (B'.re ^ 2 + B'.im ^ 2) * (n : ℝ) ^ 2 := by
    intro n hn
    have h := congrArg Complex.normSq (hrel n hn)
    rwa [map_mul, map_pow, hsq, hsq] at h
  have hcard : 6 ≤ (N.image (fun n : ℕ => (n : ℝ))).card := by
    rw [card_image_of_injective _ Nat.cast_injective]; omega
  have hnorm : Complex.normSq β = 1 := by
    by_contra hx
    have hxpos : 0 < Complex.normSq β := Complex.normSq_pos.mpr hβ0
    have hτ : Real.log (Complex.normSq β) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hxpos hx
    obtain ⟨hp0, -, -⟩ := expQuad_coeffs_eq_zero hτ hcard (fun t ht => by
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
      have hexp : Real.exp (Real.log (Complex.normSq β) * n) = Complex.normSq β ^ n := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log hxpos]
      rw [hexp]; exact hNR n hn)
    exact ha0 (pow_eq_zero_iff two_ne_zero |>.mp hp0)
  refine ⟨hnorm, ?_⟩
  have hQ : ∀ t ∈ N.image (fun n : ℕ => (n : ℝ)), (0 : ℝ) + (2 * a * (B.re - B'.re)) * t
      + ((B.re ^ 2 + B.im ^ 2) - (B'.re ^ 2 + B'.im ^ 2)) * t ^ 2 = 0 := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
    have h := hNR n hn
    rw [hnorm, one_pow, one_mul] at h
    linear_combination h
  obtain ⟨-, hc1, hc2⟩ := quadratic_eq_zero_of_three_zeros (by omega) hQ
  have hre : B'.re = B.re := by
    have h2a : 2 * a ≠ 0 := mul_ne_zero two_ne_zero ha0
    have := (mul_eq_zero.mp hc1).resolve_left h2a
    linarith
  have him : B'.im ^ 2 = B.im ^ 2 := by rw [hre] at hc2; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with him' | him'
  · -- `B' = B` forces `βⁿ = 1` on the support, hence `β = 1`
    exfalso
    have hBB : B' = B := Complex.ext hre him'
    apply hβ1
    refine hrig β fun n hn => ?_
    have h := hrel n hn
    rw [hBB] at h
    have hne : (a : ℂ) + B * n ≠ 0 := by
      rw [← hSD n hn]; exact mul_ne_zero (mem_support_iff.mp hn) (hDne n hn)
    exact (mul_eq_right₀ hne).mp h
  · -- `B' = conj B` gives the conjugation relation
    have hBB : B' = conj B := Complex.ext (by rw [hre, Complex.conj_re])
      (by rw [him', Complex.conj_im])
    intro n
    by_cases hn : n ∈ N
    · have h := hrel n hn
      have hD' := hDne n hn
      apply mul_right_cancel₀ hD'
      have e1 := hSD n hn
      calc S.coeff n * β ^ n * D n = β ^ n * (S.coeff n * D n) := by ring
        _ = (a : ℂ) + B' * n := by rw [e1, h]
        _ = conj ((a : ℂ) + B * n) := by rw [hBB]; simp
        _ = conj (S.coeff n) * D n := by rw [← e1, map_mul, hDconj]
    · rw [notMem_support_iff.mp hn]; simp

end Core

end Dixmier
