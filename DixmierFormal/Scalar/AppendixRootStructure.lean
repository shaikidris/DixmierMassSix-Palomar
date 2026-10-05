/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Companion
public import Mathlib.FieldTheory.Separable

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root structure for Appendix A

The exact scalar companion equation forces every root of its companion `f`
to be simple, independently of any support or degree bound. When all roots of
`r` have multiplicity at most two, root containment gives `r ∣ f²`.
These facts precede the factorization `r=A B²`, `f=A B C` in Proposition A.1.
-/

namespace Dixmier
open Polynomial

/-- Every root of the companion polynomial is simple. -/
theorem Comp.companion_root_simple {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    {γ : ℂ} (hfγ : f.IsRoot γ) : rootMultiplicity γ f = 1 := by
  have hf0 : f ≠ 0 := by
    have hfzero := h.f_eval_zero hr0
    intro hz
    rw [hz, eval_zero] at hfzero
    norm_num at hfzero
  have hder : (derivative f).eval γ ≠ 0 := by
    by_cases hrγ : r.IsRoot γ
    · have hslope := (h.root_slope hsρ hr0 hrγ).2
      intro hd
      rw [hd] at hslope
      norm_num at hslope
    · have hslope := h.slope_of_not_root hfγ hrγ
      intro hd
      rw [hd] at hslope
      norm_num at hslope
  have hpos : 0 < rootMultiplicity γ f := (rootMultiplicity_pos hf0).mpr hfγ
  have hle : ¬ 1 < rootMultiplicity γ f := by
    intro hgt
    have hdroot := (one_lt_rootMultiplicity_iff_isRoot hf0).mp hgt |>.2
    exact hder (by simpa [IsRoot] using hdroot)
  omega

/-- The companion is separable over `ℂ`. -/
theorem Comp.companion_separable {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1) :
    f.Separable := by
  have hf0 : f ≠ 0 := by
    intro hz
    have hh := h.f_eval_zero hr0
    rw [hz, eval_zero] at hh
    norm_num at hh
  have hnodup : f.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro γ
    by_cases hroot : f.IsRoot γ
    · rw [count_roots]
      exact le_of_eq (h.companion_root_simple hsρ hr0 hroot)
    · rw [count_roots, rootMultiplicity_eq_zero hroot]
      omega
  exact (nodup_roots_iff_of_splits hf0 (IsAlgClosed.splits f)).mp hnodup

/-- With multiplicities at most two in `r`, its root multiset embeds in
the root multiset of `f²`. -/
theorem Comp.r_dvd_companion_sq {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) : r ∣ f^2 := by
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hr0
    norm_num at hr0
  have hfne : f ≠ 0 := by
    intro hz
    have hh := h.f_eval_zero hr0
    rw [hz, eval_zero] at hh
    norm_num at hh
  apply Splits.dvd_of_roots_le_roots (IsAlgClosed.splits r) hrne
  apply Multiset.le_iff_count.mpr
  intro γ
  rw [count_roots, count_roots]
  by_cases hrγ : r.IsRoot γ
  · have hfγ := h.isRoot_f hsρ hr0 hrγ
    have hsimple := h.companion_root_simple hsρ hr0 hfγ
    rw [pow_two, rootMultiplicity_mul (mul_ne_zero hfne hfne), hsimple]
    exact hq γ
  · rw [rootMultiplicity_eq_zero hrγ]
    omega

end Dixmier
