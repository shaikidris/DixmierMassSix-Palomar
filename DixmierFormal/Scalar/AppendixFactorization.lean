/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixRootStructure

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root-multiset construction of the Appendix A factorization

Under the Appendix A multiplicity bound, the roots of `r` split into
multiplicity-one and multiplicity-two parts. The roots of the separable
companion `f` are those roots plus an extra part. Their products yield
normalized `A,B,C` with `r=A B²`, `f=A B C` and constants `1,1,-1`.
Squarefreeness and pairwise coprimality of the three factors remain to
be proved for the full Proposition A.1 contract.
-/

namespace Dixmier
open Polynomial

/-- Split the root multiset of `r` into simple and double roots. -/
theorem root_multiset_one_two (r : ℂ[X]) (hr : r ≠ 0)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) :
    r.roots =
      ((r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 1).val : Multiset ℂ) +
      ((r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 2).val : Multiset ℂ) +
      ((r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 2).val : Multiset ℂ) := by
  classical
  ext γ
  rw [count_roots, Multiset.count_add, Multiset.count_add]
  simp only [Finset.filter_val]
  simp only [Multiset.count_filter]
  have hmem : γ ∈ r.roots ↔ 0 < rootMultiplicity γ r := by
    rw [mem_roots hr, ← rootMultiplicity_pos hr]
  have hcount : Multiset.count γ r.roots.toFinset.val =
      if 0 < rootMultiplicity γ r then 1 else 0 := by
    rw [Multiset.count_eq_of_nodup (Finset.nodup _)]
    simp [hmem]
  rw [hcount]
  have hqγ := hq γ
  split_ifs <;> omega

/-- The simple roots of `f` consist of the roots of `r` and the extra
companion roots. -/
theorem companion_root_multiset_partition {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) :
    f.roots =
      ((r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 1).val : Multiset ℂ) +
      ((r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 2).val : Multiset ℂ) +
      ((f.roots.toFinset.filter fun γ => ¬ r.IsRoot γ).val : Multiset ℂ) := by
  classical
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hr0
    norm_num at hr0
  have hfne : f ≠ 0 := by
    intro hz
    have hh := h.f_eval_zero hr0
    rw [hz, eval_zero] at hh
    norm_num at hh
  ext γ
  rw [count_roots, Multiset.count_add, Multiset.count_add]
  simp only [Finset.filter_val, Multiset.count_filter]
  have hrmem : γ ∈ r.roots ↔ 0 < rootMultiplicity γ r := by
    rw [mem_roots hrne, ← rootMultiplicity_pos hrne]
  have hfmem : γ ∈ f.roots ↔ 0 < rootMultiplicity γ f := by
    rw [mem_roots hfne, ← rootMultiplicity_pos hfne]
  have hrcount : Multiset.count γ r.roots.toFinset.val =
      if 0 < rootMultiplicity γ r then 1 else 0 := by
    rw [Multiset.count_eq_of_nodup (Finset.nodup _)]
    simp [hrmem]
  have hfcount : Multiset.count γ f.roots.toFinset.val =
      if 0 < rootMultiplicity γ f then 1 else 0 := by
    rw [Multiset.count_eq_of_nodup (Finset.nodup _)]
    simp [hfmem]
  rw [hrcount, hfcount]
  by_cases hrγ : r.IsRoot γ
  · have hfγ := h.isRoot_f hsρ hr0 hrγ
    have hfsimple := h.companion_root_simple hsρ hr0 hfγ
    have hrpos : 0 < rootMultiplicity γ r := (rootMultiplicity_pos hrne).mpr hrγ
    have hqγ := hq γ
    simp only [hrγ, not_true_eq_false, ↓reduceIte, hfsimple]
    split_ifs <;> omega
  · have hrzero := rootMultiplicity_eq_zero hrγ
    change ¬ eval γ r = 0 at hrγ
    rw [hrzero]
    by_cases hfγ : f.IsRoot γ
    · have hfsimple := h.companion_root_simple hsρ hr0 hfγ
      rw [hfsimple]
      simp [hrγ]
    · have hfzero := rootMultiplicity_eq_zero hfγ
      rw [hfzero]
      simp [hrγ]

/-- The root products give an unnormalized factorization. -/
theorem appendix_raw_factorization {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) :
    ∃ A B Cc : ℂ[X],
      r = C r.leadingCoeff * A * B^2 ∧
      f = C f.leadingCoeff * A * B * Cc := by
  classical
  let S1 := r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 1
  let S2 := r.roots.toFinset.filter fun γ => rootMultiplicity γ r = 2
  let S3 := f.roots.toFinset.filter fun γ => ¬ r.IsRoot γ
  let A : ℂ[X] := (S1.val.map fun γ => X-C γ).prod
  let B : ℂ[X] := (S2.val.map fun γ => X-C γ).prod
  let Cc : ℂ[X] := (S3.val.map fun γ => X-C γ).prod
  refine ⟨A,B,Cc,?_,?_⟩
  · have hroots := root_multiset_one_two r (by
      intro hz
      rw [hz, eval_zero] at hr0
      norm_num at hr0) hq
    have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C
      ((IsAlgClosed.splits r).natDegree_eq_card_roots).symm
    rw [hroots] at hprod
    simp only [Multiset.map_add, Multiset.prod_add] at hprod
    simpa only [A,B,S1,S2, pow_two, mul_assoc] using hprod.symm
  · have hroots := companion_root_multiset_partition h hsρ hr0 hq
    have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C
      ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
    rw [hroots] at hprod
    simp only [Multiset.map_add, Multiset.prod_add] at hprod
    simpa only [A,B,Cc,S1,S2,S3, mul_assoc] using hprod.symm

/-- The exact factorization `r=A B²`, `f=A B C` with the paper's
constant-term normalization. -/
theorem appendix_normalized_factorization {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) :
    ∃ A B Cc : ℂ[X],
      A.eval 0 = 1 ∧ B.eval 0 = 1 ∧ Cc.eval 0 = -1 ∧
      r = A*B^2 ∧ f = A*B*Cc := by
  obtain ⟨A0,B0,C0,hrraw,hfraw⟩ := appendix_raw_factorization h hsρ hr0 hq
  let a := A0.eval 0
  let b := B0.eval 0
  let c := C0.eval 0
  let lr := r.leadingCoeff
  let lf := f.leadingCoeff
  have hR0 : lr*a*b^2 = 1 := by
    have hh := congrArg (eval 0) hrraw
    simp only [eval_mul, eval_C, eval_pow, hr0] at hh
    exact hh.symm
  have hF0 : lf*a*b*c = -1 := by
    have hh := h.f_eval_zero hr0
    have heval := congrArg (eval 0) hfraw
    simp only [eval_mul, eval_C, hh] at heval
    exact heval.symm
  have ha : a ≠ 0 := by intro hz; rw [hz] at hR0; norm_num at hR0
  have hb : b ≠ 0 := by intro hz; rw [hz] at hR0; norm_num at hR0
  have hc : c ≠ 0 := by intro hz; rw [hz] at hF0; norm_num at hF0
  let A : ℂ[X] := C a⁻¹ * A0
  let B : ℂ[X] := C b⁻¹ * B0
  let Cc : ℂ[X] := -C c⁻¹ * C0
  refine ⟨A,B,Cc,?_,?_,?_,?_,?_⟩
  · change (C a⁻¹ * A0).eval 0 = 1
    rw [eval_mul, eval_C]
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha
  · change (C b⁻¹ * B0).eval 0 = 1
    rw [eval_mul, eval_C]
    change b⁻¹ * b = 1
    exact inv_mul_cancel₀ hb
  · change (-C c⁻¹ * C0).eval 0 = -1
    rw [eval_mul, eval_neg, eval_C]
    change -c⁻¹ * c = -1
    calc
      -c⁻¹ * c = -(c⁻¹*c) := by ring
      _ = -1 := by rw [inv_mul_cancel₀ hc]
  · rw [hrraw]
    simp only [A,B, mul_pow, ← map_pow]
    have hab : a*b^2 ≠ 0 := mul_ne_zero ha (pow_ne_zero _ hb)
    have hRprod : lr*(a*b^2)=1 := by calc
      lr*(a*b^2) = lr*a*b^2 := by ring
      _ = 1 := hR0
    have hscalarR : lr = a⁻¹*b⁻¹^2 := by
      calc
        lr = lr*(a*b^2)*(a*b^2)⁻¹ := by field_simp [hab]
        _ = (a*b^2)⁻¹ := by rw [hRprod]; simp
        _ = a⁻¹*b⁻¹^2 := by rw [mul_inv_rev, inv_pow]; ring
    dsimp [lr] at hscalarR
    rw [hscalarR]
    simp only [map_mul]
    ring
  · rw [hfraw]
    simp only [A,B,Cc]
    have habc : a*b*c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
    have hFprod : lf*(a*b*c)=-1 := by calc
      lf*(a*b*c) = lf*a*b*c := by ring
      _ = -1 := hF0
    have hscalarF : lf = -(a⁻¹*b⁻¹*c⁻¹) := by
      calc
        lf = lf*(a*b*c)*(a*b*c)⁻¹ := by field_simp [habc]
        _ = -(a*b*c)⁻¹ := by rw [hFprod]; ring
        _ = -(a⁻¹*b⁻¹*c⁻¹) := by rw [mul_inv_rev, mul_inv_rev]; ring
    dsimp [lf] at hscalarF
    rw [hscalarF]
    simp only [map_neg, map_mul]
    ring

end Dixmier
