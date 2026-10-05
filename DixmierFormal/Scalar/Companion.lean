/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Scaling
public import DixmierFormal.Scalar.Moments
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.LinearCombination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The companion equation

`Comp ρ s r f` is the companion equation `(ρ - s) w f r' = (f + ρ w f' + 1) r` with natural
parameters.  This module proves the consequences used by the scalar classification, with no
bound on the number of terms:

* `f(0) = -1`, `f` is nonconstant, `(ρ - s) deg r = 1 + ρ deg f` and `deg f < deg r`;
* every root `α` of `r` of multiplicity `j` is a simple root of `f` with
  `α f'(α) ((ρ - s) j - ρ) = 1`; a root `γ` of `f` off the roots of `r` has `ρ γ f'(γ) = -1`;
* for fixed `r` the polynomial solution `f` is unique;
* the equation is invariant under rescaling the variable and under complex conjugation;
* the support of `r²` is root-of-unity rigid.
-/

namespace Dixmier

open Polynomial Finset ComplexConjugate

/-- The companion equation with natural parameters, in equation form. -/
def Comp (ρ s : ℕ) (r f : ℂ[X]) : Prop :=
  C ((ρ : ℂ) - s) * X * f * derivative r = (f + C (ρ : ℂ) * X * derivative f + 1) * r

theorem companionEq_natCast_iff (ρ s : ℕ) (r f : ℂ[X]) :
    CompanionEq ρ s r f ↔ Comp ρ s r f := by
  unfold CompanionEq Comp
  push_cast
  exact sub_eq_zero

/-- Coefficient of a product in the sum of two degree bounds. -/
theorem coeff_mul_of_natDegree_le' {R : Type*} [Semiring R] {p q : R[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rw [coeff_mul, Finset.sum_eq_single (m, n)]
  · rintro ⟨i, j⟩ hij hne
    rw [mem_antidiagonal] at hij
    rcases lt_trichotomy i m with h | h | h
    · rw [coeff_eq_zero_of_natDegree_lt (show q.natDegree < j by omega), mul_zero]
    · exact absurd (Prod.ext h (by simp only; omega)) hne
    · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega), zero_mul]
  · intro h; exact absurd (mem_antidiagonal.mpr rfl : (m, n) ∈ antidiagonal (m + n)) h

theorem natDegree_euler_le (p : ℂ[X]) : (euler p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_euler, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn), mul_zero]

section Basic

variable {ρ s : ℕ} {r f : ℂ[X]}

theorem Comp.euler_form (h : Comp ρ s r f) :
    C ((ρ : ℂ) - s) * (f * euler r) = (f + C (ρ : ℂ) * euler f + 1) * r := by
  unfold Comp at h; unfold euler; linear_combination h

theorem Comp.f_eval_zero (h : Comp ρ s r f) (hr0 : r.eval 0 = 1) : f.eval 0 = -1 := by
  have h0 := congrArg (eval 0) h
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_one, hr0, mul_zero, zero_mul, mul_one]
    at h0
  linear_combination -h0

theorem Comp.natDegree_f_pos (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hr : 0 < r.natDegree) : 0 < f.natDegree := by
  by_contra hf
  have hf0 : f.natDegree = 0 := by omega
  have hfC : f = C (-1) := by
    rw [eq_C_of_natDegree_eq_zero hf0, coeff_zero_eq_eval_zero, h.f_eval_zero hr0]
  unfold Comp at h
  rw [hfC, derivative_C] at h
  have hδ : ((ρ : ℂ) - s) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hsρ.ne')
  have h' : C ((ρ : ℂ) - s) * X * C (-1) * derivative r = 0 := by rw [h]; simp
  have hne : C ((ρ : ℂ) - s) * X * C (-1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hδ) X_ne_zero) (C_ne_zero.mpr (by norm_num))
  have hr' : derivative r = 0 := (mul_eq_zero.mp h').resolve_left hne
  rw [derivative_eq_zero] at hr'
  omega

/-- The integer degree identity `(ρ - s) deg r = 1 + ρ deg f`. -/
theorem Comp.degree_identity (h : Comp ρ s r f) (hsρ : s < ρ) (hr : 0 < r.natDegree)
    (hf : 0 < f.natDegree) : (ρ - s) * r.natDegree = 1 + ρ * f.natDegree := by
  have hfL : f.coeff f.natDegree ≠ 0 :=
    coeff_natDegree (p := f) ▸ leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf)
  have hre : r.coeff r.natDegree ≠ 0 :=
    coeff_natDegree (p := r) ▸ leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hr)
  set e := r.natDegree with he
  set L := f.natDegree with hL
  have hc := congrArg (fun p => p.coeff (L + e)) h.euler_form
  rw [coeff_C_mul, coeff_mul_of_natDegree_le' le_rfl (natDegree_euler_le r), coeff_euler] at hc
  have hdeg : (f + C (ρ : ℂ) * euler f + 1).natDegree ≤ L := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le le_rfl ?_) ?_
    · exact (natDegree_C_mul_le _ _).trans (natDegree_euler_le f)
    · simp
  rw [coeff_mul_of_natDegree_le' hdeg le_rfl, coeff_add, coeff_add, coeff_C_mul, coeff_euler,
    coeff_one, if_neg (by omega), add_zero] at hc
  have hmain : (((ρ : ℂ) - s) * e - (1 + ρ * L)) * (f.coeff L * r.coeff e) = 0 := by
    linear_combination hc
  have hc' := (mul_eq_zero.mp hmain).resolve_right (mul_ne_zero hfL hre)
  have : (((ρ - s) * e : ℕ) : ℂ) = ((1 + ρ * L : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hsρ.le]; linear_combination hc'
  exact_mod_cast this

theorem Comp.natDegree_f_lt (h : Comp ρ s r f) (hsρ : s < ρ) (hr : 0 < r.natDegree)
    (hf : 0 < f.natDegree) : f.natDegree < r.natDegree := by
  have hid := h.degree_identity hsρ hr hf
  by_contra hcon
  have hle : r.natDegree ≤ f.natDegree := by omega
  have h1 : (ρ - s) * r.natDegree ≤ (ρ - s) * f.natDegree := Nat.mul_le_mul_left _ hle
  have h2 : (ρ - s) * f.natDegree ≤ ρ * f.natDegree := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

end Basic

section Roots

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- Root containment and the slope at a root: every root `α` of `r` is a simple root of `f`, and
`α f'(α) ((ρ - s) j - ρ) = 1` where `j` is its multiplicity in `r`. -/
theorem Comp.root_slope (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1) {α : ℂ}
    (hα : r.IsRoot α) : f.IsRoot α ∧
      α * (derivative f).eval α * (((ρ : ℂ) - s) * (rootMultiplicity α r : ℂ) - ρ) = 1 := by
  have hr0' : r ≠ 0 := by intro hr; rw [hr, Polynomial.eval_zero] at hr0; exact zero_ne_one hr0
  have hα0 : α ≠ 0 := by rintro rfl; rw [IsRoot, hr0] at hα; exact one_ne_zero hα
  have hδ : ((ρ : ℂ) - s) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hsρ.ne')
  have hj : 0 < rootMultiplicity α r := (rootMultiplicity_pos hr0').mpr hα
  obtain ⟨u, hru, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0' α
  generalize hjdef : rootMultiplicity α r = j at hru hj ⊢
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hu : u.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  have hdr : derivative r = (X - C α) ^ k * (C ((k : ℂ) + 1) * u + (X - C α) * derivative u) := by
    rw [hru, derivative_mul, derivative_X_sub_C_pow]; push_cast; ring
  have h1 : C ((ρ : ℂ) - s) * X * f * (C ((k : ℂ) + 1) * u + (X - C α) * derivative u)
      = (f + C (ρ : ℂ) * X * derivative f + 1) * (X - C α) * u := by
    apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero α))
    have e := h
    unfold Comp at e
    rw [hdr] at e
    rw [hru] at e
    linear_combination e
  have hfα : f.eval α = 0 := by
    have e := congrArg (eval α) h1
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self, zero_mul, mul_zero,
      add_zero] at e
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hprod : ((ρ : ℂ) - s) * α * ((k : ℂ) + 1) * u.eval α * f.eval α = 0 := by
      linear_combination e
    simpa [hδ, hα0, hk1, hu] using hprod
  refine ⟨hfα, ?_⟩
  obtain ⟨g, hfg⟩ : ∃ g, f = (X - C α) * g := ⟨f /ₘ (X - C α), (mul_divByMonic_eq_iff_isRoot.mpr hfα).symm⟩
  have hdf : derivative f = g + (X - C α) * derivative g := by
    rw [hfg, derivative_mul, derivative_X_sub_C, one_mul]
  have h2 : C ((ρ : ℂ) - s) * X * g * (C ((k : ℂ) + 1) * u + (X - C α) * derivative u)
      = ((X - C α) * g + C (ρ : ℂ) * X * (g + (X - C α) * derivative g) + 1) * u := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero α)
    rw [hdf, hfg] at h1
    linear_combination h1
  have e := congrArg (eval α) h2
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self, zero_mul,
    add_zero, zero_add, eval_one] at e
  have hdfα : (derivative f).eval α = g.eval α := by
    rw [hdf]; simp
  rw [hdfα]
  have e' : (α * g.eval α * (((ρ : ℂ) - s) * ((k : ℂ) + 1) - ρ) - 1) * u.eval α = 0 := by
    linear_combination e
  push_cast
  linear_combination (mul_eq_zero.mp e').resolve_right hu

/-- Slope at a root of `f` which is not a root of `r`: `ρ γ f'(γ) = -1`. -/
theorem Comp.slope_of_not_root (h : Comp ρ s r f) {γ : ℂ} (hfγ : f.IsRoot γ)
    (hrγ : ¬ r.IsRoot γ) : (ρ : ℂ) * γ * (derivative f).eval γ = -1 := by
  have e := congrArg (eval γ) h
  rw [IsRoot] at hfγ
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_one, hfγ, mul_zero, zero_mul, zero_add]
    at e
  have e' : ((ρ : ℂ) * γ * (derivative f).eval γ + 1) * r.eval γ = 0 := by linear_combination -e
  linear_combination (mul_eq_zero.mp e').resolve_right hrγ

/-- Every root of `r` is a root of `f`. -/
theorem Comp.isRoot_f (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1) {α : ℂ}
    (hα : r.IsRoot α) : f.IsRoot α := (h.root_slope hsρ hr0 hα).1

end Roots

section Symmetry

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- For fixed `r` with `r(0) = 1`, the polynomial solution `f` is unique. -/
theorem Comp.unique {f₁ f₂ : ℂ[X]} (h₁ : Comp ρ s r f₁) (h₂ : Comp ρ s r f₂)
    (hr0 : r.eval 0 = 1) : f₁ = f₂ := by
  by_contra hne
  have hd : f₁ - f₂ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨q, hdq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (f₁ - f₂) hd 0
  generalize rootMultiplicity 0 (f₁ - f₂) = m at hdq
  simp only [map_zero, sub_zero] at hdq hndvd
  have hq0 : q.eval 0 ≠ 0 := by rwa [X_dvd_iff, coeff_zero_eq_eval_zero] at hndvd
  unfold Comp at h₁ h₂
  have hdeq : C ((ρ : ℂ) - s) * X * (X ^ m * q) * derivative r
      = (X ^ m * q + C (ρ : ℂ) * X * derivative (X ^ m * q)) * r := by
    rw [← hdq, derivative_sub]; linear_combination h₁ - h₂
  rcases m with _ | k
  · simp only [pow_zero, one_mul] at hdeq
    have e := congrArg (eval 0) hdeq
    simp [hr0] at e
    exact hq0 e.symm
  · rw [derivative_mul, derivative_X_pow] at hdeq
    have key : C ((ρ : ℂ) - s) * X * q * derivative r
        = (q + C (ρ : ℂ) * (C ((k : ℂ) + 1) * q + X * derivative q)) * r := by
      apply mul_left_cancel₀ (pow_ne_zero (k + 1) (X_ne_zero (R := ℂ)))
      push_cast at hdeq
      linear_combination hdeq
    have e := congrArg (eval 0) key
    simp only [eval_mul, eval_add, eval_C, eval_X, hr0, mul_zero, zero_mul, add_zero,
      mul_one] at e
    have e' : (1 + (ρ : ℂ) * ((k : ℂ) + 1)) * q.eval 0 = 0 := by linear_combination -e
    have hc : (1 + (ρ : ℂ) * ((k : ℂ) + 1)) ≠ 0 := by
      have : (0 : ℝ) < 1 + (ρ : ℝ) * ((k : ℝ) + 1) := by positivity
      intro h0
      have h0' : ((1 + (ρ : ℝ) * ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by push_cast; exact h0
      exact this.ne' (Complex.ofReal_eq_zero.mp h0')
    exact hq0 ((mul_eq_zero.mp e').resolve_left hc)

/-- The companion equation is invariant under rescaling the variable. -/
theorem Comp.comp_C_mul_X (h : Comp ρ s r f) (c : ℂ) :
    Comp ρ s (r.comp (C c * X)) (f.comp (C c * X)) := by
  unfold Comp at h ⊢
  have e := congrArg (fun p => p.comp (C c * X)) h
  simp only [mul_comp, add_comp, C_comp, X_comp, one_comp] at e
  rw [derivative_comp, derivative_comp, derivative_C_mul_X]
  linear_combination e

/-- The companion equation is invariant under complex conjugation of coefficients. -/
theorem Comp.map_conj (h : Comp ρ s r f) :
    Comp ρ s (r.map (starRingEnd ℂ)) (f.map (starRingEnd ℂ)) := by
  unfold Comp at h ⊢
  rw [derivative_map, derivative_map]
  have e := congrArg (Polynomial.map (starRingEnd ℂ)) h
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_natCast, map_sub, map_natCast] at e ⊢
  exact e

end Symmetry

section Rigid

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- The exponent support of `r²` is root-of-unity rigid. -/
theorem Comp.sq_support_rigid (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hr : 0 < r.natDegree) : ∀ ζ : ℂ, (∀ n ∈ (r ^ 2).support, ζ ^ n = 1) → ζ = 1 := by
  intro ζ hζ
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hf : 0 < f.natDegree := h.natDegree_f_pos hsρ hr0 hr
  have hmem : (r ^ 2).natDegree ∈ (r ^ 2).support :=
    natDegree_mem_support_of_nonzero (pow_ne_zero 2 hr0')
  have hdeg2 : (r ^ 2).natDegree = 2 * r.natDegree := by rw [natDegree_pow]
  have hζ0 : ζ ≠ 0 := by
    intro h0
    have h1 := hζ _ hmem
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hsq : (r.comp (C ζ * X)) ^ 2 = r ^ 2 := by
    rw [← pow_comp]
    ext n
    rw [coeff_comp_C_mul_X]
    by_cases hn : n ∈ (r ^ 2).support
    · rw [hζ n hn, mul_one]
    · rw [notMem_support_iff.mp hn, zero_mul]
  have hrr : r.comp (C ζ * X) = r := by
    have hprod : (r.comp (C ζ * X) - r) * (r.comp (C ζ * X) + r) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact sub_eq_zero.mp h1
    · exfalso
      have e := congrArg (eval 0) h1
      rw [eval_add, eval_zero_comp_C_mul_X, hr0, Polynomial.eval_zero] at e
      norm_num at e
  have hff : f.comp (C ζ * X) = f := by
    have h' := h.comp_C_mul_X ζ
    rw [hrr] at h'
    exact h'.unique h hr0
  have hre : ζ ^ r.natDegree = 1 := by
    have e := congrArg (fun p => p.coeff r.natDegree) hrr
    simp only [coeff_comp_C_mul_X] at e
    exact (mul_eq_left₀ (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hr0')).mp e
  have hfL : ζ ^ f.natDegree = 1 := by
    have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
    have e := congrArg (fun p => p.coeff f.natDegree) hff
    simp only [coeff_comp_C_mul_X] at e
    exact (mul_eq_left₀ (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hf0)).mp e
  have hid := h.degree_identity hsρ hr hf
  calc ζ = ζ ^ 1 * (ζ ^ f.natDegree) ^ ρ := by rw [hfL, one_pow, mul_one, pow_one]
    _ = ζ ^ (1 + ρ * f.natDegree) := by rw [pow_add, mul_comm ρ, pow_mul]
    _ = ζ ^ ((ρ - s) * r.natDegree) := by rw [hid]
    _ = 1 := by rw [mul_comm, pow_mul, hre, one_pow]

end Rigid

end Dixmier
