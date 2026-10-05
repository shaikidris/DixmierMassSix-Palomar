/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.GeneralCompanion
public import DixmierFormal.Scalar.GeneralRootDegree
public import DixmierFormal.Scalar.SparseRoots
public import DixmierFormal.Scalar.Classification

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Horizontal
open Polynomial
set_option maxHeartbeats 1000000

def HorizComp (a : ℕ) (g f : ℂ[X]) : Prop :=
  f * derivative g - C (a : ℂ) * derivative f * g = g

theorem HorizComp.natDegree_f_pos {a : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : 0 < g.natDegree) :
    0 < f.natDegree := by
  by_contra hf
  have hf0 : f.natDegree = 0 := by omega
  let c := f.coeff 0
  have hfC : f = C c := eq_C_of_natDegree_eq_zero hf0
  have heq : C c * derivative g = g := by
    have e := h
    unfold HorizComp at e
    simpa [hfC] using e
  have hle : g.natDegree ≤ (derivative g).natDegree := by
    calc
      g.natDegree = (C c * derivative g).natDegree := congrArg natDegree heq.symm
      _ ≤ (derivative g).natDegree := natDegree_C_mul_le _ _
  have hlt := natDegree_derivative_lt (Nat.ne_of_gt hg)
  omega

theorem HorizComp.root_slope {a : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : g ≠ 0) {β : ℂ} (hβ : g.IsRoot β) :
    f.IsRoot β ∧
      (((rootMultiplicity β g : ℕ) : ℂ) - a) * (derivative f).eval β = 1 := by
  have hj : 0 < rootMultiplicity β g := (rootMultiplicity_pos hg).mpr hβ
  obtain ⟨u, hgu, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg β
  generalize hjdef : rootMultiplicity β g = j at hgu hj ⊢
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hu : u.eval β ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  have hdg : derivative g = (X - C β) ^ k *
      (C ((k : ℂ) + 1) * u + (X - C β) * derivative u) := by
    rw [hgu, derivative_mul, derivative_X_sub_C_pow]; push_cast; ring
  have h1 : f * (C ((k : ℂ) + 1) * u + (X - C β) * derivative u) -
      C (a : ℂ) * derivative f * (X - C β) * u = (X - C β) * u := by
    apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero β))
    have e := h
    unfold HorizComp at e
    rw [hdg, hgu] at e
    linear_combination e
  have hfβ : f.eval β = 0 := by
    have e := congrArg (eval β) h1
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self,
      zero_mul, mul_zero, add_zero] at e
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hprod : ((k : ℂ) + 1) * u.eval β * f.eval β = 0 := by
      linear_combination e
    simpa [hk1, hu] using hprod
  refine ⟨hfβ, ?_⟩
  obtain ⟨v, hfv⟩ : ∃ v, f = (X - C β) * v :=
    ⟨f /ₘ (X - C β), (mul_divByMonic_eq_iff_isRoot.mpr hfβ).symm⟩
  have hdf : derivative f = v + (X - C β) * derivative v := by
    rw [hfv, derivative_mul, derivative_X_sub_C, one_mul]
  have h2 : v * (C ((k : ℂ) + 1) * u + (X - C β) * derivative u) -
      C (a : ℂ) * (v + (X - C β) * derivative v) * u = u := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero β)
    rw [hdf, hfv] at h1
    linear_combination h1
  have e := congrArg (eval β) h2
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self,
    zero_mul, add_zero] at e
  have hdfβ : (derivative f).eval β = v.eval β := by
    rw [hdf]; simp
  rw [hdfβ]
  have e' : ((((k : ℂ) + 1) - a) * v.eval β - 1) * u.eval β = 0 := by
    linear_combination e
  push_cast
  linear_combination (mul_eq_zero.mp e').resolve_right hu

theorem HorizComp.degree_identity_of_f_degree_ge_two {a : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : 0 < g.natDegree) (hf : 2 ≤ f.natDegree) :
    g.natDegree = a * f.natDegree := by
  set e := g.natDegree with he
  set L := f.natDegree with hL
  have htopf : f.coeff L ≠ 0 :=
    coeff_natDegree (p := f) ▸ leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt (by omega : 0 < f.natDegree))
  have htopg : g.coeff e ≠ 0 :=
    coeff_natDegree (p := g) ▸ leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt hg)
  have hfg : (f * derivative g).coeff ((L - 1) + e) =
      f.coeff L * (derivative g).coeff (e - 1) := by
    have hi : L + (e - 1) = (L - 1) + e := by omega
    rw [← hi]
    exact coeff_mul_of_natDegree_le' (le_refl L) (natDegree_derivative_le g)
  have hgf : (derivative f * g).coeff ((L - 1) + e) =
      (derivative f).coeff (L - 1) * g.coeff e := by
    exact coeff_mul_of_natDegree_le' (natDegree_derivative_le f) (le_refl e)
  have hzero : g.coeff ((L - 1) + e) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hdg : (derivative g).coeff (e - 1) = (e : ℂ) * g.coeff e := by
    rw [coeff_derivative, show e - 1 + 1 = e by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ e)]
    ring
  have hdf : (derivative f).coeff (L - 1) = (L : ℂ) * f.coeff L := by
    rw [coeff_derivative, show L - 1 + 1 = L by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    ring
  have hcg : (C (a : ℂ) * derivative f * g).coeff ((L - 1) + e) =
      (a : ℂ) * (derivative f).coeff (L - 1) * g.coeff e := by
    rw [mul_assoc, coeff_C_mul, hgf]
    ring
  have hc := congrArg (fun p : ℂ[X] => p.coeff ((L - 1) + e)) h
  rw [coeff_sub, hfg, hcg, hzero, hdg, hdf] at hc
  have hmult : (((e : ℂ) - (a : ℂ) * L) *
      (f.coeff L * g.coeff e)) = 0 := by
    linear_combination hc
  have heq : (e : ℂ) = (a : ℂ) * L := by
    have hz := (mul_eq_zero.mp hmult).resolve_right (mul_ne_zero htopf htopg)
    linear_combination hz
  exact_mod_cast heq

theorem HorizComp.exists_rootMultiplicity_gt_a {a : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : 0 < g.natDegree)
    (hae : a < g.natDegree) :
    ∃ β : ℂ, g.IsRoot β ∧ a < rootMultiplicity β g := by
  have hf := h.natDegree_f_pos hg
  obtain ⟨β, hβ, hmax⟩ := Dixmier.General.exists_max_rootMultiplicity g hg
  have hroot : ∀ γ : ℂ, g.IsRoot γ → f.IsRoot γ :=
    fun γ hγ => (h.root_slope (ne_zero_of_natDegree_gt hg) hγ).1
  have hdeg : g.natDegree ≤ rootMultiplicity β g * f.natDegree :=
    Dixmier.General.degree_le_maxMultiplicity_mul_companionDegree g f
      (rootMultiplicity β g) (ne_zero_of_natDegree_gt hg)
      (ne_zero_of_natDegree_gt hf) hroot hmax
  have hne : rootMultiplicity β g ≠ a := by
    intro heq
    have hslope := (h.root_slope (ne_zero_of_natDegree_gt hg) hβ).2
    rw [heq, sub_self, zero_mul] at hslope
    exact zero_ne_one hslope
  have hq : a ≤ rootMultiplicity β g := by
    by_cases hL : f.natDegree = 1
    · rw [hL, mul_one] at hdeg
      omega
    · have hL2 : 2 ≤ f.natDegree := by omega
      have hid := h.degree_identity_of_f_degree_ge_two hg hL2
      rw [hid] at hdeg
      exact Nat.le_of_mul_le_mul_right hdeg hf
  exact ⟨β, hβ, lt_of_le_of_ne hq (Ne.symm hne)⟩

theorem HorizComp.exists_nonzero_rootMultiplicity_gt_a {a : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : 0 < g.natDegree)
    (hae : a < g.natDegree) (hord : rootMultiplicity 0 g < a) :
    ∃ β : ℂ, β ≠ 0 ∧ g.IsRoot β ∧ a < rootMultiplicity β g := by
  obtain ⟨β, hβ, hmult⟩ := h.exists_rootMultiplicity_gt_a hg hae
  refine ⟨β, ?_, hβ, hmult⟩
  intro hzero
  subst β
  omega

theorem power_rootMultiplicity_lt_termCount
    (g : ℂ[X]) (k : ℕ) (hg : g ≠ 0) {β : ℂ} (hβ : β ≠ 0) :
    k * rootMultiplicity β g < Dixmier.termCount (g ^ k) := by
  have hdiv : ((X - C β) ^ rootMultiplicity β g) ^ k ∣ g ^ k :=
    pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd g β) k
  have hmult : k * rootMultiplicity β g ≤ rootMultiplicity β (g ^ k) :=
    (le_rootMultiplicity_iff (pow_ne_zero k hg)).mpr (by
      rw [mul_comm k (rootMultiplicity β g), pow_mul]
      exact hdiv)
  exact hmult.trans_lt (Dixmier.rootMultiplicity_lt_termCount (pow_ne_zero k hg) hβ)

theorem HorizComp.mass_six_parameters {a k : ℕ} {g f : ℂ[X]}
    (h : HorizComp a g f) (hg : 0 < g.natDegree)
    (hae : a < g.natDegree) (hord : rootMultiplicity 0 g < a)
    (hk : 2 ≤ k) (ht : Dixmier.termCount (g ^ k) ≤ 6) :
    k = 2 ∧ a = 1 ∧
      ∃ β : ℂ, β ≠ 0 ∧ g.IsRoot β ∧ rootMultiplicity β g = 2 := by
  obtain ⟨β, hβ0, hβ, hqa⟩ := h.exists_nonzero_rootMultiplicity_gt_a hg hae hord
  have hqt := power_rootMultiplicity_lt_termCount g k
    (ne_zero_of_natDegree_gt hg) hβ0
  have hq2 : 2 ≤ rootMultiplicity β g := by omega
  have hkq : 2 * rootMultiplicity β g ≤ k * rootMultiplicity β g :=
    Nat.mul_le_mul_right _ hk
  have hqk : k * 2 ≤ k * rootMultiplicity β g := Nat.mul_le_mul_left _ hq2
  have ha1 : a = 1 := by omega
  have hqeq : rootMultiplicity β g = 2 := by omega
  have hkeq : k = 2 := by omega
  exact ⟨hkeq, ha1, β, hβ0, hβ, hqeq⟩

/-- At the forced horizontal parameter `a=1`, every root is double:
the scalar slope excludes simple roots and six-term sparsity excludes
higher multiplicities. -/
theorem HorizComp.all_roots_double {g f : ℂ[X]}
    (h : HorizComp 1 g f) (hg : 0 < g.natDegree)
    (hord : rootMultiplicity 0 g < 1)
    (ht : Dixmier.termCount (g ^ 2) ≤ 6) :
    ∀ β : ℂ, g.IsRoot β → rootMultiplicity β g = 2 := by
  have hg0 : g.eval 0 ≠ 0 := by
    intro hz
    have hroot : g.IsRoot 0 := hz
    have hpos := (rootMultiplicity_pos (ne_zero_of_natDegree_gt hg)).mpr hroot
    omega
  intro β hβ
  have hpos := (rootMultiplicity_pos (ne_zero_of_natDegree_gt hg)).mpr hβ
  have hle := Dixmier.rootMultiplicity_le_two hg0 ht β
  have hne : rootMultiplicity β g ≠ 1 := by
    intro hq
    have hslope := (h.root_slope (ne_zero_of_natDegree_gt hg) hβ).2
    rw [hq] at hslope
    norm_num at hslope
  omega

end Dixmier.Horizontal
