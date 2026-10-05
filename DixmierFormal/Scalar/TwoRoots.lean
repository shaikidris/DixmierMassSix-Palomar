/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.SixTerm
public import DixmierFormal.Scalar.Scaling
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Two fourth-order roots: uniqueness and real form

Rescaling the first root to one and applying the core relation of `SixTerm` shows that two
distinct fourth-order roots of a six-term polynomial with rigid support are the only ones, and
that after one more scaling by a square root of their ratio the polynomial has real
coefficients and the two roots are nonreal conjugates on the unit circle.
-/

namespace Dixmier

open Polynomial Finset ComplexConjugate

/-- Two-root lemma for a six-term polynomial with constant coefficient one and root-of-unity
rigid support, stated with divisibility by fourth powers. -/
theorem six_term_two_roots {S : ℂ[X]} (h6 : termCount S = 6) (h1 : S.coeff 0 = 1)
    (hrig : ∀ ζ : ℂ, (∀ n ∈ S.support, ζ ^ n = 1) → ζ = 1) {α β : ℂ} (hα : α ≠ 0)
    (hαβ : α ≠ β) (hα4 : (X - C α) ^ 4 ∣ S) (hβ4 : (X - C β) ^ 4 ∣ S) :
    (∀ γ : ℂ, (X - C γ) ^ 4 ∣ S → γ = α ∨ γ = β) ∧
    ∃ c : ℂ, c ≠ 0 ∧ (∀ n : ℕ, ((S.comp (C c * X)).coeff n).im = 0) ∧
      (α / c).im ≠ 0 ∧ β / c = conj (α / c) ∧ Complex.normSq (α / c) = 1 := by
  set S₁ := S.comp (C α * X) with hS₁
  have hsupp : S₁.support = S.support := support_comp_C_mul_X hα
  have h6₁ : termCount S₁ = 6 := by rw [termCount_comp_C_mul_X hα, h6]
  have h1₁ : S₁.coeff 0 = 1 := by rw [coeff_comp_C_mul_X, h1, pow_zero, mul_one]
  have hrig₁ : ∀ ζ : ℂ, (∀ n ∈ S₁.support, ζ ^ n = 1) → ζ = 1 := by rwa [hsupp]
  have hone : (X - C 1) ^ 4 ∣ S₁ := by
    simpa [div_self hα] using pow_dvd_comp_C_mul_X hα hα4
  have hcore : ∀ γ : ℂ, (X - C γ) ^ 4 ∣ S → γ ≠ α →
      Complex.normSq (γ / α) = 1 ∧ ∀ n, S₁.coeff n * (γ / α) ^ n = conj (S₁.coeff n) := by
    intro γ hγ4 hγα
    refine normSq_eq_one_and_coeff_mul_pow_eq_conj h6₁ h1₁ hrig₁ hone
      (pow_dvd_comp_C_mul_X hα hγ4) ?_
    rwa [Ne, div_eq_one_iff_eq hα]
  obtain ⟨hnormβ, hconjβ⟩ := hcore β hβ4 (Ne.symm hαβ)
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, zero_div, map_zero] at hnormβ; exact zero_ne_one hnormβ
  refine ⟨fun γ hγ4 => ?_, ?_⟩
  · -- uniqueness of the second root
    by_cases hγα : γ = α
    · exact Or.inl hγα
    right
    obtain ⟨-, hconjγ⟩ := hcore γ hγ4 hγα
    have hratio : γ / β = 1 := by
      apply hrig
      intro n hn
      have hn₁ : S₁.coeff n ≠ 0 := by rw [← mem_support_iff, hsupp]; exact hn
      have e : S₁.coeff n * (γ / α) ^ n = S₁.coeff n * (β / α) ^ n := by
        rw [hconjγ, hconjβ]
      have e' := mul_left_cancel₀ hn₁ e
      rw [div_pow, div_pow, div_left_inj' (pow_ne_zero _ hα)] at e'
      rw [div_pow, e', div_self (pow_ne_zero _ hβ0)]
    exact (div_eq_one_iff_eq hβ0).mp hratio
  · -- real form
    obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq (β / α) (by norm_num : 0 < 2)
    have hnormη : Complex.normSq η = 1 := by
      have h := congrArg Complex.normSq hη
      rw [map_pow, hnormβ] at h
      have hnn := Complex.normSq_nonneg η
      nlinarith [sq_nonneg (Complex.normSq η - 1)]
    have hη0 : η ≠ 0 := by
      intro h; rw [h, map_zero] at hnormη; exact zero_ne_one hnormη
    have hconjη : conj η = η⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [mul_comm, Complex.mul_conj, hnormη, Complex.ofReal_one])
    refine ⟨α * η, mul_ne_zero hα hη0, fun n => ?_, ?_, ?_, ?_⟩
    · -- coefficients are real
      rw [← Complex.conj_eq_iff_im, coeff_comp_C_mul_X]
      have hc := hconjβ n
      rw [coeff_comp_C_mul_X] at hc
      calc conj (S.coeff n * (α * η) ^ n) = conj (S.coeff n * α ^ n) * (conj η) ^ n := by
            rw [mul_pow, ← mul_assoc, map_mul, map_pow]
        _ = S.coeff n * α ^ n * (β / α) ^ n * η⁻¹ ^ n := by rw [← hc, hconjη]
        _ = S.coeff n * (α * η) ^ n := by
            have e : (η ^ 2) ^ n = η ^ n * η ^ n := by rw [← pow_mul, two_mul, pow_add]
            have hηn : η ^ n ≠ 0 := pow_ne_zero _ hη0
            rw [← hη, e, inv_pow, mul_pow]
            calc S.coeff n * α ^ n * (η ^ n * η ^ n) * (η ^ n)⁻¹
                = S.coeff n * α ^ n * η ^ n * (η ^ n * (η ^ n)⁻¹) := by ring
              _ = S.coeff n * (α ^ n * η ^ n) := by rw [mul_inv_cancel₀ hηn, mul_one]; ring
    · -- `α / c = conj η` is nonreal
      have hαc : α / (α * η) = conj η := by rw [hconjη, div_mul_eq_div_div, div_self hα, one_div]
      rw [hαc, Complex.conj_im, neg_ne_zero]
      intro him
      have hre : (η.re : ℂ) = η := by rw [← Complex.conj_eq_iff_re, Complex.conj_eq_iff_im]; exact him
      have hsq : η.re ^ 2 = 1 := by
        have h := hnormη
        rw [Complex.normSq_apply, him, mul_zero, add_zero] at h
        linarith
      have hη2 : η ^ 2 = 1 := by
        rw [← hre]; exact_mod_cast hsq
      rw [hη2, eq_comm, div_eq_one_iff_eq hα] at hη
      exact hαβ hη.symm
    · -- `β / c = η = conj (α / c)`
      have hαc : α / (α * η) = conj η := by rw [hconjη, div_mul_eq_div_div, div_self hα, one_div]
      rw [hαc, Complex.conj_conj, div_mul_eq_div_div, div_eq_iff hη0, ← pow_two, hη]
    · have hαc : α / (α * η) = conj η := by rw [hconjη, div_mul_eq_div_div, div_self hα, one_div]
      rw [hαc, Complex.normSq_conj, hnormη]

end Dixmier
