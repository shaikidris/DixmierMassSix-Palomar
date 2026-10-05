/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Companion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The general negative-crossing scalar equation

This module formalizes the polynomial equation
`δ w f r' = (H f + W w f' + 1) r` used before the mass-six
parameters reduce to `(H,W)=(1,ρ)`. It proves the constant-term
relation, positivity and degree comparison of `f`, and containment of
the roots of `r` in the roots of `f`, with the exact root-slope identity.
No mass or degree cutoff is assumed.
-/

namespace Dixmier.General
open Polynomial Finset
set_option maxHeartbeats 1000000

/-- General polynomial companion equation, with natural parameters. -/
def GenComp (δ H W : ℕ) (r f : ℂ[X]) : Prop :=
  C (δ : ℂ) * X * f * derivative r =
    (C (H : ℂ) * f + C (W : ℂ) * X * derivative f + 1) * r

/-- At `r(0)=1`, the constant coefficient satisfies `H f(0)+1=0`. -/
theorem GenComp.constant_relation {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) (hr0 : r.eval 0 = 1) :
    (H : ℂ) * f.eval 0 + 1 = 0 := by
  have h0 := congrArg (eval 0) h
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_one, hr0,
    mul_zero, zero_mul, mul_one] at h0
  linear_combination -h0

theorem GenComp.euler_form {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) :
    C (δ : ℂ) * (f * euler r) =
      (C (H : ℂ) * f + C (W : ℂ) * euler f + 1) * r := by
  unfold GenComp at h
  unfold euler
  linear_combination h

/-- A nonconstant normalized `r` forces a nonconstant companion. -/
theorem GenComp.natDegree_f_pos {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) (hδ : 0 < δ)
    (hr0 : r.eval 0 = 1) (hr : 0 < r.natDegree) :
    0 < f.natDegree := by
  by_contra hf
  have hf0 : f.natDegree = 0 := by omega
  let c := f.coeff 0
  have hfC : f = C c := eq_C_of_natDegree_eq_zero hf0
  have hcRel : (H : ℂ) * c + 1 = 0 := by
    simpa only [c, coeff_zero_eq_eval_zero] using h.constant_relation hr0
  have hcne : c ≠ 0 := by
    intro hc
    rw [hc] at hcRel
    norm_num at hcRel
  have hδne : (δ : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hδ
  unfold GenComp at h
  rw [hfC, derivative_C] at h
  have hsum : C (H : ℂ) * C c + C (W : ℂ) * X * 0 + 1 = (0 : ℂ[X]) := by
    calc
      C (H : ℂ) * C c + C (W : ℂ) * X * 0 + 1 = C ((H : ℂ) * c + 1) := by simp
      _ = 0 := by rw [hcRel]; simp
  rw [hsum, zero_mul] at h
  have hprefix : C (δ : ℂ) * X * C c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hδne) X_ne_zero) (C_ne_zero.mpr hcne)
  have hr' : derivative r = 0 := (mul_eq_zero.mp h).resolve_left hprefix
  rw [derivative_eq_zero] at hr'
  omega

/-- The exact leading-degree identity `δ deg r = H + W deg f`. -/
theorem GenComp.degree_identity {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f)
    (hr : 0 < r.natDegree) (hf : 0 < f.natDegree) :
    δ * r.natDegree = H + W * f.natDegree := by
  have hfL : f.coeff f.natDegree ≠ 0 :=
    coeff_natDegree (p := f) ▸ leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf)
  have hre : r.coeff r.natDegree ≠ 0 :=
    coeff_natDegree (p := r) ▸ leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hr)
  set e := r.natDegree with he
  set L := f.natDegree with hL
  have hc := congrArg (fun p => p.coeff (L + e)) h.euler_form
  rw [coeff_C_mul, coeff_mul_of_natDegree_le' le_rfl (natDegree_euler_le r), coeff_euler] at hc
  have hdeg : (C (H : ℂ) * f + C (W : ℂ) * euler f + 1).natDegree ≤ L := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · exact natDegree_C_mul_le _ _
    · exact (natDegree_C_mul_le _ _).trans (natDegree_euler_le f)
    · simp
  rw [coeff_mul_of_natDegree_le' hdeg le_rfl, coeff_add, coeff_add, coeff_C_mul,
    coeff_C_mul, coeff_euler, coeff_one, if_neg (by omega), add_zero] at hc
  have hmain : (((δ : ℂ) * e - ((H : ℂ) + W * L)) *
      (f.coeff L * r.coeff e)) = 0 := by
    linear_combination hc
  have hc' := (mul_eq_zero.mp hmain).resolve_right (mul_ne_zero hfL hre)
  have : (((δ * e : ℕ) : ℂ) = ((H + W * L : ℕ) : ℂ)) := by
    push_cast
    linear_combination hc'
  exact_mod_cast this

theorem GenComp.natDegree_f_lt {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) (hH : 0 < H) (hδW : δ ≤ W)
    (hr : 0 < r.natDegree) (hf : 0 < f.natDegree) :
    f.natDegree < r.natDegree := by
  have hid := h.degree_identity hr hf
  by_contra hcon
  have hle : r.natDegree ≤ f.natDegree := by omega
  have h1 : δ * r.natDegree ≤ δ * f.natDegree := Nat.mul_le_mul_left _ hle
  have h2 : δ * f.natDegree ≤ W * f.natDegree := Nat.mul_le_mul_right _ hδW
  omega

/-- Every root of `r` is a root of `f`; the derivative at that root obeys
the displayed slope equation. -/
theorem GenComp.root_slope {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) (hδ : 0 < δ) (hr0 : r.eval 0 = 1)
    {α : ℂ} (hα : r.IsRoot α) :
    f.IsRoot α ∧
      α * (derivative f).eval α *
        ((δ : ℂ) * (rootMultiplicity α r : ℂ) - W) = 1 := by
  have hr0' : r ≠ 0 := by intro hr; rw [hr, Polynomial.eval_zero] at hr0; exact zero_ne_one hr0
  have hα0 : α ≠ 0 := by rintro rfl; rw [IsRoot, hr0] at hα; exact one_ne_zero hα
  have hδne : (δ : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hδ
  have hj : 0 < rootMultiplicity α r := (rootMultiplicity_pos hr0').mpr hα
  obtain ⟨u, hru, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0' α
  generalize hjdef : rootMultiplicity α r = j at hru hj ⊢
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hu : u.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  have hdr : derivative r = (X - C α) ^ k *
      (C ((k : ℂ) + 1) * u + (X - C α) * derivative u) := by
    rw [hru, derivative_mul, derivative_X_sub_C_pow]; push_cast; ring
  have h1 : C (δ : ℂ) * X * f *
      (C ((k : ℂ) + 1) * u + (X - C α) * derivative u) =
      (C (H : ℂ) * f + C (W : ℂ) * X * derivative f + 1) * (X - C α) * u := by
    apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero α))
    have e := h
    unfold GenComp at e
    rw [hdr, hru] at e
    linear_combination e
  have hfα : f.eval α = 0 := by
    have e := congrArg (eval α) h1
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self,
      zero_mul, mul_zero, add_zero] at e
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hprod : (δ : ℂ) * α * ((k : ℂ) + 1) * u.eval α * f.eval α = 0 := by
      linear_combination e
    simpa [hδne, hα0, hk1, hu] using hprod
  refine ⟨hfα, ?_⟩
  obtain ⟨g, hfg⟩ : ∃ g, f = (X - C α) * g :=
    ⟨f /ₘ (X - C α), (mul_divByMonic_eq_iff_isRoot.mpr hfα).symm⟩
  have hdf : derivative f = g + (X - C α) * derivative g := by
    rw [hfg, derivative_mul, derivative_X_sub_C, one_mul]
  have h2 : C (δ : ℂ) * X * g *
      (C ((k : ℂ) + 1) * u + (X - C α) * derivative u) =
      (C (H : ℂ) * ((X - C α) * g) +
        C (W : ℂ) * X * (g + (X - C α) * derivative g) + 1) * u := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero α)
    rw [hdf, hfg] at h1
    linear_combination h1
  have e := congrArg (eval α) h2
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self,
    zero_mul, mul_zero, add_zero, zero_add, eval_one] at e
  have hdfα : (derivative f).eval α = g.eval α := by
    rw [hdf]; simp
  rw [hdfα]
  have e' : (α * g.eval α * ((δ : ℂ) * ((k : ℂ) + 1) - W) - 1) * u.eval α = 0 := by
    linear_combination e
  push_cast
  linear_combination (mul_eq_zero.mp e').resolve_right hu

theorem GenComp.isRoot_f {δ H W : ℕ} {r f : ℂ[X]}
    (h : GenComp δ H W r f) (hδ : 0 < δ) (hr0 : r.eval 0 = 1)
    {α : ℂ} (hα : r.IsRoot α) : f.IsRoot α :=
  (h.root_slope hδ hr0 hα).1

end Dixmier.General
