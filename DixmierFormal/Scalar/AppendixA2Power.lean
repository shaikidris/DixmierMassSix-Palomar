/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA2Scaling

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.2: full support of every power

The alternating coefficients of the normalized factor become positive
real coefficients after `X ↦ -X`. Positive polynomial products have no
gaps in their degree interval, so every power is dense. The general
linear-factor scaling theorem transports the exact term count back to
the original scalar factorization, with no degree or power cutoff.
-/

namespace Dixmier
open Polynomial

theorem positive_coeff_mul {p q : ℝ[X]} {d e : ℕ}
    (hpd : p.natDegree ≤ d) (hqe : q.natDegree ≤ e)
    (hp : ∀ i ≤ d, 0 < p.coeff i)
    (hq : ∀ j ≤ e, 0 < q.coeff j) :
    ∀ n ≤ d+e, 0 < (p*q).coeff n := by
  intro n hn
  rw [coeff_mul]
  apply (Finset.sum_pos_iff_of_nonneg ?_).mpr
  · let i := min n d
    let j := n-i
    have hi : i ≤ d := min_le_right ..
    have hi' : i ≤ n := min_le_left ..
    have hj : j ≤ e := by dsimp [i,j]; omega
    refine ⟨(i,j), ?_, mul_pos (hp i hi) (hq j hj)⟩
    exact Finset.mem_antidiagonal.mpr (by dsimp [j]; omega)
  · intro x hx
    rcases x with ⟨i,j⟩
    by_cases hid : i ≤ d
    · by_cases hje : j ≤ e
      · exact (mul_pos (hp i hid) (hq j hje)).le
      · have hz : q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hz]
    · have hz : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hz]

theorem positive_coeff_pow {p : ℝ[X]} {d : ℕ}
    (hpd : p.natDegree ≤ d) (hp : ∀ i ≤ d, 0 < p.coeff i) (k : ℕ) :
    ∀ n ≤ k*d, 0 < (p^k).coeff n := by
  induction k with
  | zero =>
      intro n hn
      have hn0 : n=0 := by omega
      subst n
      simp
  | succ k ih =>
      have hkdeg : (p^k).natDegree ≤ k*d := by
        exact natDegree_pow_le.trans (Nat.mul_le_mul_left k hpd)
      have hmul := positive_coeff_mul hkdeg hpd ih hp
      intro n hn
      have hn' : n ≤ k*d+d := by simpa [Nat.succ_mul] using hn
      simpa only [pow_succ] using hmul n hn'

noncomputable def realCoeffs (S : ℂ[X]) : ℝ[X] :=
  S.sum fun n a => monomial n a.re

theorem realCoeffs_coeff (S : ℂ[X]) (n : ℕ) :
    (realCoeffs S).coeff n = (S.coeff n).re := by
  simp [realCoeffs, coeff_monomial, Polynomial.sum,
    Finset.sum_ite_eq', mem_support_iff]
  intro hz
  simp [hz]

theorem realCoeffs_map {S : ℂ[X]}
    (hreal : ∀ n : ℕ, (S.coeff n).im = 0) :
    (realCoeffs S).map Complex.ofRealHom = S := by
  ext n
  rw [coeff_map, realCoeffs_coeff]
  have hi := hreal n
  simpa [hi] using (Complex.re_add_im (S.coeff n))

theorem signed_B_to_positive {B : ℂ[X]} {D : ℕ}
    (hdeg : B.natDegree ≤ D)
    (hsign : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      B.coeff n = (((-1 : ℝ)^n * x : ℝ) : ℂ)) :
    let S := B.comp (C (-1 : ℂ)*X)
    (∀ n ≤ D, 0 < (realCoeffs S).coeff n) ∧
    (∀ n : ℕ, (S.coeff n).im = 0) := by
  dsimp
  have hS : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      (B.comp (C (-1 : ℂ)*X)).coeff n = (x : ℂ) := by
    intro n hn
    obtain ⟨x,hx,hcoeff⟩ := hsign n hn
    refine ⟨x,hx,?_⟩
    rw [coeff_comp_C_mul_X, hcoeff]
    push_cast
    calc
      ((-1 : ℂ)^n*x)*(-1 : ℂ)^n = x*((-1 : ℂ)^n)^2 := by ring
      _ = x := by rw [← pow_mul]; simp [mul_comm n 2, pow_mul]
  constructor
  · intro n hn
    obtain ⟨x,hx,hxn⟩ := hS n hn
    rw [realCoeffs_coeff, hxn]
    simpa using hx
  · intro n
    by_cases hn : n ≤ D
    · obtain ⟨x,hx,hxn⟩ := hS n hn
      rw [hxn]
      simp
    · have hz : B.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [coeff_comp_C_mul_X, hz]
      simp

theorem signed_dense_power_coeff_nonzero {B : ℂ[X]} {D : ℕ}
    (hdeg : B.natDegree ≤ D)
    (hsign : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      B.coeff n = (((-1 : ℝ)^n * x : ℝ) : ℂ))
    (k n : ℕ) (hn : n ≤ k*D) : (B^k).coeff n ≠ 0 := by
  let S := B.comp (C (-1 : ℂ)*X)
  let R := realCoeffs S
  obtain ⟨hRpos,hSreal⟩ := signed_B_to_positive hdeg hsign
  have hmap : R.map Complex.ofRealHom = S := realCoeffs_map hSreal
  have hRdeg : R.natDegree ≤ D := by
    have hinj : Function.Injective (Complex.ofRealHom : ℝ →+* ℂ) :=
      Complex.ofReal_injective
    have hdegree : R.natDegree = S.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj, hmap]
    rw [hdegree]
    exact (natDegree_comp_C_mul_X (p := B) (by norm_num : (-1 : ℂ) ≠ 0)).le.trans hdeg
  have hp := positive_coeff_pow hRdeg hRpos k n hn
  have hSco : (S^k).coeff n = ((R^k).coeff n : ℂ) := by
    rw [← hmap]
    have hpowmap : (R^k).map Complex.ofRealHom = (R.map Complex.ofRealHom)^k := by
      induction k with
      | zero => simp
      | succ k ih => simp [pow_succ]
    rw [← hpowmap, coeff_map]
    simp
  have hSnonzero : (S^k).coeff n ≠ 0 := by
    rw [hSco]
    exact_mod_cast (ne_of_gt hp)
  have hscale : (S^k).coeff n = (B^k).coeff n * (-1 : ℂ)^n := by
    change ((B.comp (C (-1 : ℂ)*X))^k).coeff n = _
    rw [← pow_comp, coeff_comp_C_mul_X]
  intro hz
  apply hSnonzero
  rw [hscale, hz]
  simp

theorem signed_dense_power_termCount {B : ℂ[X]} {D : ℕ}
    (hdeg : B.natDegree ≤ D)
    (hsign : ∀ n ≤ D, ∃ x : ℝ, 0 < x ∧
      B.coeff n = (((-1 : ℝ)^n * x : ℝ) : ℂ))
    (k : ℕ) : termCount (B^k) = k*D+1 := by
  have hpowdeg : (B^k).natDegree ≤ k*D :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left k hdeg)
  have hsupp : (B^k).support = Finset.range (k*D+1) := by
    ext n
    simp only [mem_support_iff, Finset.mem_range]
    constructor
    · intro hnon
      by_contra hn
      exact hnon (coeff_eq_zero_of_natDegree_lt (by omega))
    · intro hn
      exact signed_dense_power_coeff_nonzero hdeg hsign k n (by omega)
  unfold termCount
  rw [hsupp]
  simp

theorem appendix_A2_normalized_termCount {ρ s : ℕ} {B : ℂ[X]}
    (hsρ : s < ρ) (hB0 : B.eval 0 = 1) (hD : 0 < B.natDegree)
    (hcomp : Comp ρ s (B^2) (B*(X-1))) (k : ℕ) :
    termCount ((B^2)^k) = 2*B.natDegree*k+1 := by
  have hgt := appendix_A2_h_gt_one hsρ hB0 hD hcomp
  let h : ℕ := ρ-2*s
  have hh : 2 ≤ h := by dsimp [h]; omega
  have hBne : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have heq := appendix_A2_equation_from_comp hsρ hBne hD hcomp
  have hcast : (ρ : ℂ)-2*(s : ℂ) = (h : ℂ) := by
    dsimp [h]
    rw [Nat.cast_sub (by omega : 2*s ≤ ρ)]
    push_cast
    ring
  rw [hcast] at heq
  have hsign := appendix_A2_alternating_coefficients hh hB0 heq
  have htc := signed_dense_power_termCount (le_refl B.natDegree) hsign (2*k)
  calc
    termCount ((B^2)^k) = termCount (B^(2*k)) := by rw [pow_mul]
    _ = (2*k)*B.natDegree+1 := htc
    _ = 2*B.natDegree*k+1 := by ring

theorem appendix_A2_complete {ρ s : ℕ} {B Cc : ℂ[X]}
    (hsρ : s < ρ) (hCdeg : Cc.natDegree = 1)
    (hC0 : Cc.eval 0 = -1) (hB0 : B.eval 0 = 1)
    (hD : 2 ≤ B.natDegree)
    (hcomp : Comp ρ s (B^2) (B*Cc)) :
    2*s+1 < ρ ∧ ∀ k : ℕ,
      termCount ((B^2)^k) = 2*B.natDegree*k+1 := by
  obtain ⟨Bn,hcompn,hdegn,hB0n,hpres⟩ :=
    appendix_A2_normalize_general_linear hCdeg hC0 hB0 hcomp
  have hDn : 0 < Bn.natDegree := by omega
  constructor
  · exact appendix_A2_h_gt_one hsρ hB0n hDn hcompn
  · intro k
    have htc := appendix_A2_normalized_termCount hsρ hB0n hDn hcompn k
    have hpres' := hpres k
    rw [pow_mul, pow_mul] at hpres'
    rw [← hpres', htc, hdegn]

theorem appendix_A2_not_seven {ρ s : ℕ} {B Cc : ℂ[X]}
    (hsρ : s < ρ) (hCdeg : Cc.natDegree = 1)
    (hC0 : Cc.eval 0 = -1) (hB0 : B.eval 0 = 1)
    (hD : 2 ≤ B.natDegree)
    (hcomp : Comp ρ s (B^2) (B*Cc)) :
    termCount ((B^2)^2) ≠ 7 := by
  have htc := (appendix_A2_complete hsρ hCdeg hC0 hB0 hD hcomp).2 2
  omega

end Dixmier
