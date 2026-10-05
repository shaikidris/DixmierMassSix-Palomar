/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.LinearCombination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Zeros of an exponential times a quadratic minus a quadratic

Rolle's theorem, iterated three times, bounds the number of real zeros of
`t ↦ exp(τ t) P(t) - Q(t)` for real quadratics `P, Q` and `τ ≠ 0`: six distinct zeros force
`P = 0`.  This is the analytic step that puts the two fourth-order roots of a six-term
polynomial on a common circle.
-/

namespace Dixmier

open Finset

/-- Rolle counting: if `f` vanishes on a finite set `s`, then `f'` vanishes on a finite set with
at least `card s - 1` elements. -/
theorem exists_finset_deriv_eq_zero {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (s : Finset ℝ) (hs : ∀ x ∈ s, f x = 0) :
    ∃ t : Finset ℝ, (∀ y ∈ t, f' y = 0) ∧ s.card ≤ t.card + 1 := by
  classical
  have key : ∀ p : ℝ × ℝ, p.1 < p.2 → f p.1 = 0 → f p.2 = 0 →
      ∃ c ∈ Set.Ioo p.1 p.2, f' c = 0 := fun p hlt h1 h2 =>
    exists_hasDerivAt_eq_zero hlt (fun z _ => (hf z).continuousAt.continuousWithinAt)
      (h1.trans h2.symm) (fun z _ => hf z)
  let c : ℝ × ℝ → ℝ := fun p =>
    if h : p.1 < p.2 ∧ f p.1 = 0 ∧ f p.2 = 0 then Classical.choose (key p h.1 h.2.1 h.2.2) else 0
  have hc : ∀ p : ℝ × ℝ, p.1 < p.2 → f p.1 = 0 → f p.2 = 0 →
      c p ∈ Set.Ioo p.1 p.2 ∧ f' (c p) = 0 := by
    intro p hlt h1 h2
    have h : p.1 < p.2 ∧ f p.1 = 0 ∧ f p.2 = 0 := ⟨hlt, h1, h2⟩
    simp only [c, dif_pos h]
    exact Classical.choose_spec (key p hlt h1 h2)
  refine ⟨((s ×ˢ s).filter fun p => p.1 < p.2).image c, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    obtain ⟨hps, hlt⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_product.mp hps
    exact (hc p hlt (hs _ h1) (hs _ h2)).2
  · refine card_le_of_interleaved fun x hx y hy hxy _ => ?_
    refine ⟨c (x, y), mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩,
      ?_⟩
    exact (hc (x, y) hxy (hs x hx) (hs y hy)).1

/-- Derivative of `exp(τ t)(a₀ + a₁ t + a₂ t²) - (c₀ + c₁ t + c₂ t²)`. -/
theorem hasDerivAt_expQuad (τ a0 a1 a2 c0 c1 c2 t : ℝ) :
    HasDerivAt (fun t => Real.exp (τ * t) * (a0 + a1 * t + a2 * t ^ 2) - (c0 + c1 * t + c2 * t ^ 2))
      (Real.exp (τ * t) * ((τ * a0 + a1) + (τ * a1 + 2 * a2) * t + τ * a2 * t ^ 2)
        - (c1 + 2 * c2 * t + 0 * t ^ 2)) t := by
  have he : HasDerivAt (fun t => Real.exp (τ * t)) (Real.exp (τ * t) * τ) t := by
    simpa using ((hasDerivAt_id t).const_mul τ).exp
  have hpoly : ∀ b0 b1 b2 : ℝ,
      HasDerivAt (fun t => b0 + b1 * t + b2 * t ^ 2) (b1 + 2 * b2 * t) t := by
    intro b0 b1 b2
    have h : HasDerivAt (fun t => b0 + b1 * t + b2 * t ^ 2)
        (0 + b1 * 1 + b2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      ((hasDerivAt_const t b0).add ((hasDerivAt_id' t).const_mul b1)).add
        ((hasDerivAt_pow 2 t).const_mul b2)
    exact h.congr_deriv (by norm_num; ring)
  exact ((he.mul (hpoly a0 a1 a2)).sub (hpoly c0 c1 c2)).congr_deriv (by ring)

/-- A real quadratic with three distinct zeros vanishes identically. -/
theorem quadratic_eq_zero_of_three_zeros {c0 c1 c2 : ℝ} {s : Finset ℝ} (hs : 3 ≤ s.card)
    (h : ∀ y ∈ s, c0 + c1 * y + c2 * y ^ 2 = 0) : c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < s.card)
  have e1 : (x - y) * (c1 + c2 * (x + y)) = 0 := by linear_combination h x hx - h y hy
  have e2 : (x - z) * (c1 + c2 * (x + z)) = 0 := by linear_combination h x hx - h z hz
  have f1 := (mul_eq_zero.mp e1).resolve_left (sub_ne_zero.mpr hxy)
  have f2 := (mul_eq_zero.mp e2).resolve_left (sub_ne_zero.mpr hxz)
  have e3 : (y - z) * c2 = 0 := by linear_combination f1 - f2
  have hc2 := (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hyz)
  have hc1 : c1 = 0 := by linear_combination f1 - (x + y) * hc2
  have hc0 : c0 = 0 := by linear_combination h x hx - x * hc1 - x ^ 2 * hc2
  exact ⟨hc0, hc1, hc2⟩

/-- Six distinct zeros of `exp(τ t) P(t) - Q(t)`, with `τ ≠ 0` and `P, Q` real quadratics,
force `P = 0`. -/
theorem expQuad_coeffs_eq_zero {τ : ℝ} (hτ : τ ≠ 0) {p0 p1 p2 q0 q1 q2 : ℝ} {s : Finset ℝ}
    (hs : 6 ≤ s.card)
    (hz : ∀ t ∈ s, Real.exp (τ * t) * (p0 + p1 * t + p2 * t ^ 2) = q0 + q1 * t + q2 * t ^ 2) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 := by
  obtain ⟨s1, hs1, hc1⟩ := exists_finset_deriv_eq_zero
    (fun t => hasDerivAt_expQuad τ p0 p1 p2 q0 q1 q2 t) s (fun t ht => by simp [hz t ht])
  obtain ⟨s2, hs2, hc2⟩ := exists_finset_deriv_eq_zero
    (fun t => hasDerivAt_expQuad τ (τ * p0 + p1) (τ * p1 + 2 * p2) (τ * p2) q1 (2 * q2) 0 t) s1
    (fun t ht => by linear_combination hs1 t ht)
  obtain ⟨s3, hs3, hc3⟩ := exists_finset_deriv_eq_zero
    (fun t => hasDerivAt_expQuad τ (τ * (τ * p0 + p1) + (τ * p1 + 2 * p2))
      (τ * (τ * p1 + 2 * p2) + 2 * (τ * p2)) (τ * (τ * p2)) (2 * q2) (2 * 0) 0 t) s2
    (fun t ht => by linear_combination hs2 t ht)
  have hquad : ∀ y ∈ s3, (τ ^ 3 * p0 + 3 * τ ^ 2 * p1 + 6 * τ * p2)
      + (τ ^ 3 * p1 + 6 * τ ^ 2 * p2) * y + (τ ^ 3 * p2) * y ^ 2 = 0 := by
    intro y hy
    have hy' := hs3 y hy
    have hexp : Real.exp (τ * y) ≠ 0 := (Real.exp_pos _).ne'
    have hmul : Real.exp (τ * y) * ((τ ^ 3 * p0 + 3 * τ ^ 2 * p1 + 6 * τ * p2)
        + (τ ^ 3 * p1 + 6 * τ ^ 2 * p2) * y + (τ ^ 3 * p2) * y ^ 2) = 0 := by
      linear_combination hy'
    exact (mul_eq_zero.mp hmul).resolve_left hexp
  obtain ⟨h0, h1, h2⟩ := quadratic_eq_zero_of_three_zeros (by omega) hquad
  have hτ3 : τ ^ 3 ≠ 0 := pow_ne_zero 3 hτ
  have hp2 : p2 = 0 := (mul_eq_zero.mp h2).resolve_left hτ3
  have hp1 : p1 = 0 := by
    have : τ ^ 3 * p1 = 0 := by linear_combination h1 - 6 * τ ^ 2 * hp2
    exact (mul_eq_zero.mp this).resolve_left hτ3
  have hp0 : p0 = 0 := by
    have : τ ^ 3 * p0 = 0 := by linear_combination h0 - 3 * τ ^ 2 * hp1 - 6 * τ * hp2
    exact (mul_eq_zero.mp this).resolve_left hτ3
  exact ⟨hp0, hp1, hp2⟩

end Dixmier
