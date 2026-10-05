/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Companion
public import DixmierFormal.Scalar.TwoRoots
public import DixmierFormal.Scalar.RealRoots
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The scalar classification

For the companion equation with `t(r²) ≤ 6`: every root of `r` is simple or double
(`rootMultiplicity_le_two`), some root is double (`Comp.exists_double_root`), and exactly one root
is double (`Comp.eq_of_double_roots`, via the five- and six-term root lemmas, the real form and
the first-root sign argument).  Scaling the double root to one, the coefficient recurrence has
strictly alternating signs, so `t(r²) = 2 deg r + 1`, forcing `deg r = 2`.
-/

namespace Dixmier

open Polynomial Finset ComplexConjugate

section Multiplicities

/-- Divisibility over `ℂ` from a comparison of root multiplicities. -/
theorem dvd_of_forall_rootMultiplicity_le {p q : ℂ[X]} (hp : p ≠ 0)
    (h : ∀ α, rootMultiplicity α p ≤ rootMultiplicity α q) : p ∣ q :=
  Splits.dvd_of_roots_le_roots (IsAlgClosed.splits p) hp
    (Multiset.le_iff_count.mpr fun α => by rw [count_roots, count_roots]; exact h α)

/-- Root multiplicities under rescaling of the variable. -/
theorem rootMultiplicity_comp_C_mul_X {p : ℂ[X]} (hp : p ≠ 0) {c : ℂ} (hc : c ≠ 0) (β : ℂ) :
    rootMultiplicity β (p.comp (C c * X)) = rootMultiplicity (c * β) p := by
  have hp' : p.comp (C c * X) ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.comp (C c⁻¹ * X)) h0
    simp only [comp_C_mul_X_comp_C_inv_mul_X p hc, zero_comp] at this
    exact hp this
  apply le_antisymm
  · rw [le_rootMultiplicity_iff hp]
    have h1 := pow_dvd_comp_C_mul_X (inv_ne_zero hc)
      ((le_rootMultiplicity_iff hp').mp (le_refl (rootMultiplicity β (p.comp (C c * X)))))
    rwa [comp_C_mul_X_comp_C_inv_mul_X p hc, div_inv_eq_mul, mul_comm] at h1
  · rw [le_rootMultiplicity_iff hp']
    have h1 := pow_dvd_comp_C_mul_X hc
      ((le_rootMultiplicity_iff hp).mp (le_refl (rootMultiplicity (c * β) p)))
    rwa [mul_div_cancel_left₀ _ hc] at h1

/-- If `t(r²) ≤ 6` and `r(0) ≠ 0`, every root of `r` has multiplicity at most two. -/
theorem rootMultiplicity_le_two {r : ℂ[X]} (hr0 : r.eval 0 ≠ 0) (ht : termCount (r ^ 2) ≤ 6)
    (α : ℂ) : rootMultiplicity α r ≤ 2 := by
  have hr0' : r ≠ 0 := by rintro rfl; simp at hr0
  by_cases hα : α = 0
  · subst hα
    rw [rootMultiplicity_eq_zero (by simpa [IsRoot] using hr0)]
    exact Nat.zero_le _
  have h2 : rootMultiplicity α (r ^ 2) = 2 * rootMultiplicity α r := by
    rw [pow_two, rootMultiplicity_mul (mul_ne_zero hr0' hr0'), two_mul]
  have := rootMultiplicity_lt_termCount (pow_ne_zero 2 hr0') hα
  omega

end Multiplicities

section DoubleRoot

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- Some root of `r` is at least double. -/
theorem Comp.exists_double_root (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hr : 0 < r.natDegree) : ∃ α, 2 ≤ rootMultiplicity α r := by
  by_contra hcon
  push Not at hcon
  have hf := h.natDegree_f_pos hsρ hr0 hr
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hdvd : r ∣ f := dvd_of_forall_rootMultiplicity_le hr0' fun α => by
    by_cases hα : r.IsRoot α
    · have h1 := hcon α
      have h2 : 1 ≤ rootMultiplicity α f :=
        (rootMultiplicity_pos hf0).mpr (h.isRoot_f hsρ hr0 hα)
      omega
    · rw [rootMultiplicity_eq_zero hα]; exact Nat.zero_le _
  have h1 := natDegree_le_of_dvd hdvd hf0
  have h2 := h.natDegree_f_lt hsρ hr hf
  omega

end DoubleRoot

section UniqueDouble

variable {ρ s : ℕ} {r f : ℂ[X]}

theorem eval_ofReal_map_ofRealHom (q : ℝ[X]) (x : ℝ) :
    (q.map Complex.ofRealHom).eval (x : ℂ) = ((q.eval x : ℝ) : ℂ) := by
  rw [eval_map, show (x : ℂ) = Complex.ofRealHom x from rfl, eval₂_at_apply]
  rfl

theorem real_of_map_conj_eq {p : ℂ[X]} (hp : p.map (starRingEnd ℂ) = p) (n : ℕ) :
    (p.coeff n).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← coeff_map, hp]

/-- At most one root of `r` is double. -/
theorem Comp.eq_of_double_roots (h : Comp ρ s r f) (hs : 1 ≤ s) (hsρ : s < ρ)
    (hr0 : r.eval 0 = 1) (hr : 0 < r.natDegree) (ht : termCount (r ^ 2) ≤ 6) {α β : ℂ}
    (hα : 2 ≤ rootMultiplicity α r) (hβ : 2 ≤ rootMultiplicity β r) : α = β := by
  by_contra hαβ
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hf : 0 < f.natDegree := h.natDegree_f_pos hsρ hr0 hr
  have hnz : ∀ γ : ℂ, 2 ≤ rootMultiplicity γ r → γ ≠ 0 := by
    intro γ hγ h0
    subst h0
    have hroot : r.IsRoot 0 := (rootMultiplicity_pos hr0').mp (by omega)
    rw [IsRoot, hr0] at hroot
    exact one_ne_zero hroot
  have hα0 := hnz α hα
  have hβ0 := hnz β hβ
  have h4 : ∀ γ : ℂ, 2 ≤ rootMultiplicity γ r → (X - C γ) ^ 4 ∣ r ^ 2 := by
    intro γ hγ
    have h2 : (X - C γ) ^ 2 ∣ r := (le_rootMultiplicity_iff hr0').mp hγ
    have h22 := pow_dvd_pow_of_dvd h2 2
    rwa [← pow_mul] at h22
  have hα4 := h4 α hα
  have hβ4 := h4 β hβ
  have hS1 : (r ^ 2).coeff 0 = 1 := by rw [coeff_zero_eq_eval_zero, eval_pow, hr0, one_pow]
  have hrig := h.sq_support_rigid hsρ hr0 hr
  have ht5 : 4 < termCount (r ^ 2) := pow_dvd_imp_lt_termCount (pow_ne_zero 2 hr0') hα0 hα4
  rcases (show termCount (r ^ 2) = 5 ∨ termCount (r ^ 2) = 6 by omega) with h5 | h6
  · exact hαβ (eq_of_five_terms h5 (by rw [hS1]; exact one_ne_zero) hrig hβ0 hα4 hβ4)
  obtain ⟨huniq, c, hc0, hreal, hαc, hβc, -⟩ :=
    six_term_two_roots h6 hS1 hrig hα0 hαβ hα4 hβ4
  set r₂ := r.comp (C c * X) with hr₂
  set f₂ := f.comp (C c * X) with hf₂
  have h₂ : Comp ρ s r₂ f₂ := h.comp_C_mul_X c
  have hr₂0 : r₂.eval 0 = 1 := by rw [hr₂, eval_zero_comp_C_mul_X, hr0]
  have hr₂ne : r₂ ≠ 0 := by
    intro h0; rw [h0, Polynomial.eval_zero] at hr₂0; exact zero_ne_one hr₂0
  -- `r₂` is real
  have hsq_real : ∀ n, ((r₂ ^ 2).coeff n).im = 0 := by
    intro n; rw [hr₂, ← pow_comp]; exact hreal n
  have hr₂conj : r₂.map (starRingEnd ℂ) = r₂ := by
    have hsqconj : (r₂.map (starRingEnd ℂ)) ^ 2 = r₂ ^ 2 := by
      rw [← Polynomial.map_pow]
      ext n
      rw [coeff_map]
      exact Complex.conj_eq_iff_im.mpr (hsq_real n)
    have hprod : (r₂.map (starRingEnd ℂ) - r₂) * (r₂.map (starRingEnd ℂ) + r₂) = 0 := by
      linear_combination hsqconj
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact sub_eq_zero.mp h1
    · exfalso
      have e := congrArg (fun p => p.coeff 0) h1
      simp only [coeff_add, coeff_map, coeff_zero] at e
      rw [coeff_zero_eq_eval_zero, hr₂0, map_one] at e
      norm_num at e
  -- `f₂` is real
  have hf₂conj : f₂.map (starRingEnd ℂ) = f₂ := by
    have h' := h₂.map_conj
    rw [hr₂conj] at h'
    exact h'.unique h₂ hr₂0
  obtain ⟨F, hF⟩ := exists_map_ofReal_eq (real_of_map_conj_eq hf₂conj)
  obtain ⟨R, hR⟩ := exists_map_ofReal_eq (real_of_map_conj_eq hr₂conj)
  have hevF : ∀ x : ℝ, f₂.eval (x : ℂ) = ((F.eval x : ℝ) : ℂ) := fun x => by
    rw [← hF, eval_ofReal_map_ofRealHom]
  have hevR : ∀ x : ℝ, r₂.eval (x : ℂ) = ((R.eval x : ℝ) : ℂ) := fun x => by
    rw [← hR, eval_ofReal_map_ofRealHom]
  have hevdF : ∀ x : ℝ, (derivative f₂).eval (x : ℂ) = (((derivative F).eval x : ℝ) : ℂ) :=
    fun x => by rw [← hF, derivative_map, eval_ofReal_map_ofRealHom]
  -- real roots of `r₂` are simple
  have hr₂mult : ∀ x : ℝ, rootMultiplicity (x : ℂ) r₂ ≤ 1 := by
    intro x
    by_contra hgt
    have h2 : 2 ≤ rootMultiplicity (x : ℂ) r₂ := by omega
    rw [hr₂, rootMultiplicity_comp_C_mul_X hr0' hc0] at h2
    rcases huniq _ (h4 _ h2) with h1 | h1
    · apply hαc
      rw [← h1, mul_div_cancel_left₀ _ hc0, Complex.ofReal_im]
    · apply hαc
      have hαβc : α / c = conj (β / c) := by rw [hβc, Complex.conj_conj]
      rw [hαβc, ← h1, mul_div_cancel_left₀ _ hc0, Complex.conj_ofReal, Complex.ofReal_im]
  -- slopes at the real roots of `F`
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le s) hsρ)
  have hslope : ∀ γ : ℝ, F.IsRoot γ → γ * (derivative F).eval γ < 0 := by
    intro γ hγ
    have hγc : f₂.IsRoot (γ : ℂ) := by
      rw [IsRoot, hevF, show F.eval γ = 0 from hγ, Complex.ofReal_zero]
    by_cases hrγ : r₂.IsRoot (γ : ℂ)
    · have hj : rootMultiplicity (γ : ℂ) r₂ = 1 :=
        le_antisymm (hr₂mult γ) ((rootMultiplicity_pos hr₂ne).mpr hrγ)
      have hsl := (h₂.root_slope hsρ hr₂0 hrγ).2
      rw [hj, hevdF] at hsl
      have hre : γ * (derivative F).eval γ * (-(s : ℝ)) = 1 := by
        have hc' : ((γ * (derivative F).eval γ * (-(s : ℝ)) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          push_cast; linear_combination hsl
        exact_mod_cast hc'
      nlinarith
    · have hsl := h₂.slope_of_not_root hγc hrγ
      rw [hevdF] at hsl
      have hre : (ρ : ℝ) * γ * (derivative F).eval γ = -1 := by
        have hc' : (((ρ : ℝ) * γ * (derivative F).eval γ : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
          push_cast; linear_combination hsl
        exact_mod_cast hc'
      nlinarith
  have hF0 : F.eval 0 < 0 := by
    have e := hevF 0
    rw [Complex.ofReal_zero, h₂.f_eval_zero hr₂0] at e
    have e' : F.eval 0 = -1 := by exact_mod_cast e.symm
    linarith
  have hFno := forall_not_isRoot_of_slope_neg hF0 hslope
  have hRno : ∀ x, ¬ R.IsRoot x := by
    intro x hx
    have hrx : r₂.IsRoot (x : ℂ) := by
      rw [IsRoot, hevR, show R.eval x = 0 from hx, Complex.ofReal_zero]
    have hfx := h₂.isRoot_f hsρ hr₂0 hrx
    apply hFno x
    rw [IsRoot, hevF] at hfx
    exact_mod_cast hfx
  have hFe := even_natDegree_of_forall_not_isRoot hFno
  have hRe := even_natDegree_of_forall_not_isRoot hRno
  have hinj : Function.Injective Complex.ofRealHom := Complex.ofRealHom.injective
  have hFdeg : F.natDegree = f.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hF, hf₂, natDegree_comp_C_mul_X hc0]
  have hRdeg : R.natDegree = r.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hR, hr₂, natDegree_comp_C_mul_X hc0]
  have hid := h.degree_identity hsρ hr hf
  obtain ⟨a, ha⟩ := hRe
  obtain ⟨b, hb⟩ := hFe
  rw [hRdeg] at ha
  rw [hFdeg] at hb
  have e1 : (ρ - s) * r.natDegree = 2 * ((ρ - s) * a) := by rw [ha]; ring
  have e2 : ρ * f.natDegree = 2 * (ρ * b) := by rw [hb]; ring
  omega

end UniqueDouble

section Recurrence

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- With the double root at one and all other roots simple, `r = (X - 1) f`. -/
theorem Comp.eq_X_sub_one_mul (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hr : 0 < r.natDegree) (h1 : rootMultiplicity 1 r = 2)
    (hother : ∀ α, α ≠ 1 → rootMultiplicity α r ≤ 1) : r = (X - C 1) * f := by
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hf := h.natDegree_f_pos hsρ hr0 hr
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hg0 : (X - C 1) * f ≠ 0 := mul_ne_zero (X_sub_C_ne_zero 1) hf0
  have hdvd : r ∣ (X - C 1) * f := dvd_of_forall_rootMultiplicity_le hr0' fun α => by
    rw [rootMultiplicity_mul hg0]
    by_cases hα1 : α = 1
    · subst hα1
      have hroot : r.IsRoot 1 := (rootMultiplicity_pos hr0').mp (by omega)
      have hf1 : 1 ≤ rootMultiplicity 1 f := (rootMultiplicity_pos hf0).mpr (h.isRoot_f hsρ hr0 hroot)
      rw [h1, rootMultiplicity_X_sub_C_self]
      omega
    · have hle := hother α hα1
      by_cases hα : r.IsRoot α
      · have hfα : 1 ≤ rootMultiplicity α f :=
          (rootMultiplicity_pos hf0).mpr (h.isRoot_f hsρ hr0 hα)
        omega
      · rw [rootMultiplicity_eq_zero hα]; exact Nat.zero_le _
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hg0 hq
  have hdeg1 : ((X - C 1) * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero 1) hf0, natDegree_X_sub_C]; ring
  have hdeg2 : ((X - C 1) * f).natDegree = r.natDegree + q.natDegree := by
    rw [hq, natDegree_mul hr0' hq0]
  have hlt := h.natDegree_f_lt hsρ hr hf
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have e := congrArg (eval 0) hq
  rw [eval_mul, eval_mul, hr0, eval_sub, eval_X, eval_C, h.f_eval_zero hr0, hqC, eval_C] at e
  have hq1 : q.coeff 0 = 1 := by linear_combination -e
  rw [hqC, hq1, C_1, mul_one] at hq
  exact hq.symm

/-- The real sequence solving the coefficient recurrence of `f`. -/
noncomputable def recSeq (s L : ℕ) : ℕ → ℝ
  | 0 => -1
  | (j + 1) => (-((s : ℝ) * ((L : ℝ) - j)) * recSeq s L j + if j = 0 then 1 else 0) /
      (1 + (s : ℝ) * (j + 1))

theorem recSeq_succ (s L j : ℕ) : recSeq s L (j + 1) =
    (-((s : ℝ) * ((L : ℝ) - j)) * recSeq s L j + if j = 0 then 1 else 0) /
      (1 + (s : ℝ) * (j + 1)) := rfl

/-- Alternating signs of the recurrence up to `L`. -/
theorem recSeq_sign {s L : ℕ} (hs : 1 ≤ s) (hL : 1 ≤ L) :
    ∀ j ≤ L, 0 < (-1 : ℝ) ^ (j + 1) * recSeq s L j := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  intro j
  induction j with
  | zero => intro _; simp [recSeq]
  | succ j ih =>
    intro hj
    have hden : (0 : ℝ) < 1 + (s : ℝ) * (j + 1) := by positivity
    have hLj : (0 : ℝ) < (L : ℝ) - j := by
      have : (j : ℝ) + 1 ≤ L := by exact_mod_cast hj
      linarith
    rw [recSeq_succ]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · norm_num [recSeq]
      positivity
    · rw [if_neg (by omega), add_zero]
      have hprev := ih (by omega)
      have key : (-1 : ℝ) ^ (j + 1 + 1) * (-((s : ℝ) * ((L : ℝ) - j)) * recSeq s L j /
          (1 + (s : ℝ) * (j + 1)))
          = ((s : ℝ) * ((L : ℝ) - j)) / (1 + (s : ℝ) * (j + 1)) *
            ((-1 : ℝ) ^ (j + 1) * recSeq s L j) := by
        rw [pow_succ]; field_simp
      rw [key]
      exact mul_pos (div_pos (mul_pos hs' hLj) hden) hprev

theorem recSeq_eq_zero {s L : ℕ} (hL : 1 ≤ L) : ∀ j, L < j → recSeq s L j = 0 := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rw [recSeq_succ, if_neg (by omega), add_zero]
    rcases Nat.lt_or_ge L j with hLj | hLj
    · rw [ih hLj, mul_zero, zero_div]
    · have : j = L := by omega
      subst this
      simp

/-- With the double root at one and all other roots simple, `r²` has `2 deg r + 1` terms, and
`ρ = s deg r + 1`. -/
theorem Comp.termCount_sq_ge (h : Comp ρ s r f) (hs : 1 ≤ s) (hsρ : s < ρ)
    (hr0 : r.eval 0 = 1) (hr : 0 < r.natDegree) (h1 : rootMultiplicity 1 r = 2)
    (hother : ∀ α, α ≠ 1 → rootMultiplicity α r ≤ 1) :
    ρ = s * r.natDegree + 1 ∧ 2 * r.natDegree + 1 ≤ termCount (r ^ 2) ∧
      (∀ j, f.coeff j = (recSeq s (r.natDegree - 1) j : ℂ)) := by
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hf := h.natDegree_f_pos hsρ hr0 hr
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hrf := h.eq_X_sub_one_mul hsρ hr0 hr h1 hother
  have hdegr : r.natDegree = f.natDegree + 1 := by
    rw [hrf, natDegree_mul (X_sub_C_ne_zero 1) hf0, natDegree_X_sub_C]; ring
  have hid := h.degree_identity hsρ hr hf
  set e := r.natDegree with he
  set L := f.natDegree with hL
  have hρ : ρ = s * e + 1 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsρ.le
    rw [Nat.add_sub_cancel_left, hdegr] at hid
    rw [hdegr]
    ring_nf at hid ⊢
    linarith
  refine ⟨hρ, ?_⟩
  -- reduced equation for `f`
  have hred : C ((ρ : ℂ) - s) * (X * f + X * euler f - euler f)
      = (f + C (ρ : ℂ) * euler f + 1) * X - (f + C (ρ : ℂ) * euler f + 1) := by
    have e1 := h
    unfold Comp at e1
    rw [hrf, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      C_1] at e1
    apply mul_right_cancel₀ hf0
    unfold euler
    linear_combination e1
  have hρc : (ρ : ℂ) = s * e + 1 := by rw [hρ]; push_cast; ring
  have heL : (e : ℂ) = L + 1 := by rw [hdegr]; push_cast; ring
  have hrec : ∀ j : ℕ, (1 + (s : ℂ) * (j + 1)) * f.coeff (j + 1)
      = -((s : ℂ) * ((L : ℂ) - j)) * f.coeff j + (if j = 0 then 1 else 0) := by
    intro j
    have e1 := congrArg (fun p => p.coeff (j + 1)) hred
    simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_mul_X, coeff_euler,
      coeff_one] at e1
    rw [if_neg (Nat.succ_ne_zero j)] at e1
    rw [hρc, heL] at e1
    split_ifs at e1 ⊢ with hj0
    · subst hj0; push_cast at e1 ⊢; linear_combination e1
    · push_cast at e1 ⊢; linear_combination e1
  have hLpos : 1 ≤ L := hf
  have hL' : e - 1 = L := by omega
  have hfx : ∀ j, f.coeff j = (recSeq s L j : ℂ) := by
    intro j
    induction j with
    | zero => rw [coeff_zero_eq_eval_zero, h.f_eval_zero hr0]; simp [recSeq]
    | succ j ih =>
      have hden : (1 + (s : ℂ) * (j + 1)) ≠ 0 := by
        have : (0 : ℝ) < 1 + (s : ℝ) * (j + 1) := by positivity
        exact_mod_cast this.ne'
      apply mul_left_cancel₀ hden
      rw [hrec j, ih, recSeq_succ]
      push_cast
      rw [mul_div_cancel₀ _ hden]
      split_ifs <;> simp
  refine ⟨?_, by rw [hL']; exact hfx⟩
  -- coefficients of `r`
  set y : ℕ → ℝ := fun k => if k = 0 then 1 else recSeq s L (k - 1) - recSeq s L k with hy
  have hry : ∀ k, r.coeff k = (y k : ℂ) := by
    intro k
    rw [hrf, C_1, sub_mul, one_mul, coeff_sub, hy]
    rcases k with _ | k
    · simp [hfx, recSeq]
    · rw [coeff_X_mul, hfx, hfx]; simp
  have hsign : ∀ k ≤ e, 0 < (-1 : ℝ) ^ k * y k := by
    intro k hk
    rcases k with _ | k
    · simp [hy]
    · simp only [hy, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
      have h1' := recSeq_sign hs hLpos k (by omega)
      have h2' : 0 ≤ (-1 : ℝ) ^ (k + 1 + 1) * recSeq s L (k + 1) := by
        rcases Nat.lt_or_ge L (k + 1) with hlt | hge
        · rw [recSeq_eq_zero hLpos _ hlt, mul_zero]
        · exact (recSeq_sign hs hLpos (k + 1) hge).le
      have expand : (-1 : ℝ) ^ (k + 1) * (recSeq s L k - recSeq s L (k + 1))
          = (-1 : ℝ) ^ (k + 1) * recSeq s L k + (-1) ^ (k + 1 + 1) * recSeq s L (k + 1) := by
        rw [pow_succ (-1 : ℝ) (k + 1)]; ring
      rw [expand]
      linarith
  have hyz : ∀ k, e < k → y k = 0 := by
    intro k hk
    have hc := hry k
    rw [coeff_eq_zero_of_natDegree_lt hk] at hc
    exact_mod_cast hc.symm
  have hsqc : ∀ n, (r ^ 2).coeff n = ((∑ p ∈ antidiagonal n, y p.1 * y p.2 : ℝ) : ℂ) := by
    intro n; rw [pow_two, coeff_mul]; push_cast; simp only [hry]
  have hnz : ∀ n ≤ 2 * e, (r ^ 2).coeff n ≠ 0 := by
    intro n hn
    rw [hsqc]
    have hpos : 0 < (-1 : ℝ) ^ n * ∑ p ∈ antidiagonal n, y p.1 * y p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_pos'
      · intro p hp
        rw [mem_antidiagonal] at hp
        have hfac : (-1 : ℝ) ^ n * (y p.1 * y p.2) = ((-1) ^ p.1 * y p.1) * ((-1) ^ p.2 * y p.2) := by
          rw [← hp, pow_add]; ring
        rw [hfac]
        have hnn : ∀ k, 0 ≤ (-1 : ℝ) ^ k * y k := by
          intro k
          rcases Nat.lt_or_ge e k with hk | hk
          · rw [hyz k hk, mul_zero]
          · exact (hsign k hk).le
        exact mul_nonneg (hnn _) (hnn _)
      · refine ⟨(min n e, n - min n e), by rw [mem_antidiagonal]; omega, ?_⟩
        have hfac : (-1 : ℝ) ^ n * (y (min n e) * y (n - min n e))
            = ((-1) ^ (min n e) * y (min n e)) * ((-1) ^ (n - min n e) * y (n - min n e)) := by
          calc (-1 : ℝ) ^ n * (y (min n e) * y (n - min n e))
              = (-1 : ℝ) ^ (min n e + (n - min n e)) * (y (min n e) * y (n - min n e)) := by
                rw [Nat.add_sub_cancel' (min_le_left n e)]
            _ = _ := by rw [pow_add]; ring
        rw [hfac]
        exact mul_pos (hsign _ (min_le_right n e)) (hsign _ (by omega))
    intro h0
    rw [Complex.ofReal_eq_zero] at h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hsub : range (2 * e + 1) ⊆ (r ^ 2).support := by
    intro n hn
    rw [mem_range] at hn
    exact mem_support_iff.mpr (hnz n (by omega))
  have := Finset.card_le_card hsub
  rw [card_range] at this
  exact this

end Recurrence

section Main

variable {ρ s : ℕ} {r f : ℂ[X]}

/-- The scalar classification with natural parameters. -/
theorem Comp.classification (h : Comp ρ s r f) (hs : 1 ≤ s) (hsρ : s < ρ)
    (hr : 0 < r.natDegree) (hr0 : r.eval 0 = 1) (ht : termCount (r ^ 2) ≤ 6) :
    ρ = 2 * s + 1 ∧ (∃ lam : ℂ, lam ≠ 0 ∧ r = (1 - C lam * X) ^ 2 ∧ f = C lam * X - 1) ∧
      termCount (r ^ 2) = 5 := by
  have hr0' : r ≠ 0 := ne_zero_of_natDegree_gt hr
  obtain ⟨α₀, hα₀⟩ := h.exists_double_root hsρ hr0 hr
  have hle2 := rootMultiplicity_le_two (by rw [hr0]; exact one_ne_zero) ht
  have hα₀2 : rootMultiplicity α₀ r = 2 := le_antisymm (hle2 α₀) hα₀
  have hα₀0 : α₀ ≠ 0 := by
    rintro rfl
    have hroot : r.IsRoot 0 := (rootMultiplicity_pos hr0').mp (by omega)
    rw [IsRoot, hr0] at hroot
    exact one_ne_zero hroot
  have hother : ∀ β, β ≠ α₀ → rootMultiplicity β r ≤ 1 := by
    intro β hβ
    by_contra hgt
    exact hβ (h.eq_of_double_roots hs hsρ hr0 hr ht (by omega) hα₀)
  have hdeg2 : 2 ≤ r.natDegree := by
    have hdvd : (X - C α₀) ^ 2 ∣ r := (le_rootMultiplicity_iff hr0').mp hα₀
    have := natDegree_le_of_dvd hdvd hr0'
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
  set r₁ := r.comp (C α₀ * X) with hr₁def
  set f₁ := f.comp (C α₀ * X) with hf₁def
  have h₁ : Comp ρ s r₁ f₁ := h.comp_C_mul_X α₀
  have hr₁0 : r₁.eval 0 = 1 := by rw [hr₁def, eval_zero_comp_C_mul_X, hr0]
  have hr₁deg : r₁.natDegree = r.natDegree := natDegree_comp_C_mul_X hα₀0
  have ht₁ : termCount (r₁ ^ 2) = termCount (r ^ 2) := by
    rw [hr₁def, ← pow_comp, termCount_comp_C_mul_X hα₀0]
  have h1₁ : rootMultiplicity 1 r₁ = 2 := by
    rw [hr₁def, rootMultiplicity_comp_C_mul_X hr0' hα₀0, mul_one, hα₀2]
  have hother₁ : ∀ β, β ≠ 1 → rootMultiplicity β r₁ ≤ 1 := by
    intro β hβ
    rw [hr₁def, rootMultiplicity_comp_C_mul_X hr0' hα₀0]
    refine hother _ fun h' => hβ ?_
    have h'' : α₀ * β = α₀ * 1 := by rw [h', mul_one]
    exact mul_left_cancel₀ hα₀0 h''
  have hr₁pos : 0 < r₁.natDegree := by rw [hr₁deg]; exact hr
  obtain ⟨hρ, hcount, hfx⟩ := h₁.termCount_sq_ge hs hsρ hr₁0 hr₁pos h1₁ hother₁
  have he2 : r.natDegree = 2 := by
    rw [hr₁deg, ht₁] at hcount
    omega
  rw [hr₁deg, he2] at hρ hfx
  have hrf₁ := h₁.eq_X_sub_one_mul hsρ hr₁0 hr₁pos h1₁ hother₁
  have hf₁0 : f₁ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hrf₁; rw [hrf₁] at hr₁pos; simp at hr₁pos
  have hf₁deg : f₁.natDegree = 1 := by
    have hd := congrArg natDegree hrf₁
    rw [natDegree_mul (X_sub_C_ne_zero 1) hf₁0, natDegree_X_sub_C, hr₁deg, he2] at hd
    omega
  have hs1 : (1 : ℝ) + s ≠ 0 := by positivity
  have hf₁ : f₁ = X - 1 := by
    rw [eq_X_add_C_of_natDegree_le_one hf₁deg.le, hfx 1, hfx 0]
    have hv1 : recSeq s (2 - 1) 1 = 1 := by
      rw [show (2 : ℕ) - 1 = 1 from rfl, recSeq_succ, if_pos rfl]
      simp only [recSeq, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one, zero_add]
      field_simp
      ring
    rw [hv1]
    simp [recSeq, sub_eq_add_neg]
  have hr₁ : r₁ = (X - 1) ^ 2 := by rw [hrf₁, hf₁, C_1]; ring
  have hinv : ∀ p : ℂ[X], p = (p.comp (C α₀ * X)).comp (C α₀⁻¹ * X) :=
    fun p => (comp_C_mul_X_comp_C_inv_mul_X p hα₀0).symm
  refine ⟨by rw [hρ]; ring, ⟨α₀⁻¹, inv_ne_zero hα₀0, ?_, ?_⟩, ?_⟩
  · rw [hinv r, ← hr₁def, hr₁]
    simp only [pow_comp, sub_comp, X_comp, one_comp]
    ring
  · rw [hinv f, ← hf₁def, hf₁]
    simp only [sub_comp, X_comp, one_comp]
  · have hle : termCount (r ^ 2) ≤ 5 := by
      rw [← ht₁, hr₁]
      unfold termCount
      have hX1 : (X - 1 : ℂ[X]).natDegree ≤ 1 := by rw [← C_1]; exact natDegree_X_sub_C_le 1
      have hdeg : (((X - 1 : ℂ[X]) ^ 2) ^ 2).natDegree ≤ 4 := by
        rw [← pow_mul]
        refine natDegree_pow_le.trans ?_
        calc (2 * 2) * (X - 1 : ℂ[X]).natDegree ≤ (2 * 2) * 1 := Nat.mul_le_mul_left _ hX1
          _ = 4 := by norm_num
      calc (((X - 1 : ℂ[X]) ^ 2) ^ 2).support.card
          ≤ (range ((((X - 1 : ℂ[X]) ^ 2) ^ 2).natDegree + 1)).card :=
            Finset.card_le_card supp_subset_range_natDegree_succ
        _ ≤ 5 := by rw [card_range]; omega
    have hge : 5 ≤ termCount (r ^ 2) := by rw [← ht₁]; omega
    omega

end Main

end Dixmier
