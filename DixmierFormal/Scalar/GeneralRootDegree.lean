/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.GeneralCompanion
public import Mathlib.Analysis.Complex.Polynomial.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root multiplicity versus companion degree

Over `ℂ`, the degree is the sum of root multiplicities. If all roots of
`r` also belong to `f`, the maximum multiplicity bounds the ratio of
their degrees. This is the finite-root counting step in paper Lemma 5.1.
-/

namespace Dixmier.General
open Polynomial Finset

theorem degree_le_maxMultiplicity_mul_companionDegree
    (r f : ℂ[X]) (q : ℕ)
    (hr : r ≠ 0) (hf : f ≠ 0)
    (hroot : ∀ α : ℂ, r.IsRoot α → f.IsRoot α)
    (hq : ∀ α : ℂ, r.IsRoot α → rootMultiplicity α r ≤ q) :
    r.natDegree ≤ q * f.natDegree := by
  classical
  let S := r.roots.toFinset
  let T := f.roots.toFinset
  have he : r.natDegree = ∑ α ∈ S, rootMultiplicity α r := by
    rw [← IsAlgClosed.card_roots_eq_natDegree]
    simpa only [S, count_roots] using (Multiset.toFinset_sum_count_eq r.roots).symm
  have hsum : (∑ α ∈ S, rootMultiplicity α r) ≤ ∑ _α ∈ S, q := by
    apply Finset.sum_le_sum
    intro α hα
    exact hq α ((mem_roots hr).mp (Multiset.mem_toFinset.mp hα))
  have hST : S ⊆ T := by
    intro α hα
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hf).mpr
    exact hroot α ((mem_roots hr).mp (Multiset.mem_toFinset.mp hα))
  have hS : S.card ≤ f.natDegree :=
    (Finset.card_mono hST).trans ((Multiset.toFinset_card_le _).trans (card_roots' f))
  calc
    r.natDegree = ∑ α ∈ S, rootMultiplicity α r := he
    _ ≤ S.card * q := by simpa using hsum
    _ ≤ f.natDegree * q := Nat.mul_le_mul_right q hS
    _ = q * f.natDegree := Nat.mul_comm _ _

/-- Root-count form of the homogeneous-companion argument after the
substitution `w = X^ρ`. A face root is either the origin or lies above a
root of `r`; the companion polynomial `X * f(X^ρ)` then contains every
distinct face root. The bound is independent of root multiplicities. -/
theorem substituted_companion_root_count
    (S r f : ℂ[X]) (ρ : ℕ) (hρ : 0 < ρ)
    (hS : S ≠ 0) (hf : f ≠ 0)
    (hroot : ∀ α : ℂ, r.IsRoot α → f.IsRoot α)
    (hface : ∀ z : ℂ, S.IsRoot z → z = 0 ∨ r.IsRoot (z ^ ρ)) :
    S.roots.toFinset.card ≤ 1 + ρ * f.natDegree := by
  classical
  let T : ℂ[X] := X * f.comp (X ^ ρ)
  have hT : T ≠ 0 := by
    have hcomp : f.comp (X ^ ρ) ≠ 0 := by
      intro hz
      rcases (comp_eq_zero_iff.mp hz) with hfzero | hconstant
      · exact hf hfzero
      · have hdegree : ρ = 0 := by
          simpa only [natDegree_X_pow, natDegree_C] using
            congrArg natDegree hconstant.2
        omega
    exact mul_ne_zero X_ne_zero hcomp
  have hsubset : S.roots.toFinset ⊆ T.roots.toFinset := by
    intro z hz
    have hzS : S.IsRoot z := (mem_roots hS).mp (Multiset.mem_toFinset.mp hz)
    have hzT : T.IsRoot z := by
      rcases hface z hzS with rfl | hrz
      · simp [T, IsRoot]
      · have hfz := hroot (z ^ ρ) hrz
        change f.eval (z ^ ρ) = 0 at hfz
        change (X * f.comp (X ^ ρ)).eval z = 0
        simp [hfz]
    exact Multiset.mem_toFinset.mpr ((mem_roots hT).mpr hzT)
  have hdegree : T.natDegree ≤ 1 + ρ * f.natDegree := by
    calc
      T.natDegree ≤ (X : ℂ[X]).natDegree + (f.comp (X ^ ρ)).natDegree :=
        natDegree_mul_le
      _ ≤ 1 + f.natDegree * ρ := by
        simpa using Nat.add_le_add_left
          (natDegree_comp_le (p := f) (q := (X : ℂ[X]) ^ ρ)) 1
      _ = 1 + ρ * f.natDegree := by rw [Nat.mul_comm]
  exact (Finset.card_mono hsubset).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' T).trans hdegree))

/-- The scalar companion equation supplies the root-containment hypothesis
of `substituted_companion_root_count`. -/
theorem GenComp.substituted_companion_root_count
    {δ H W : ℕ} {r f S : ℂ[X]} (h : GenComp δ H W r f)
    (hδ : 0 < δ) (hr0 : r.eval 0 = 1) (hf : f ≠ 0)
    (ρ : ℕ) (hρ : 0 < ρ) (hS : S ≠ 0)
    (hface : ∀ z : ℂ, S.IsRoot z → z = 0 ∨ r.IsRoot (z ^ ρ)) :
    S.roots.toFinset.card ≤ 1 + ρ * f.natDegree :=
  Dixmier.General.substituted_companion_root_count S r f ρ hρ hS hf
    (fun _α hα => GenComp.isRoot_f h hδ hr0 hα) hface

/-- In the source-shaped face `ν X^b r(X^ρ)^k`, every root is either zero
or projects to a root of `r`. This removes the abstract root-location
hypothesis from the preceding companion count. -/
theorem GenComp.powered_face_root_count
    {δ H W : ℕ} {r f S : ℂ[X]} (h : GenComp δ H W r f)
    (hδ : 0 < δ) (hr0 : r.eval 0 = 1) (hf : f ≠ 0)
    (ρ b k : ℕ) (hρ : 0 < ρ) (ν : ℂ) (hS : S ≠ 0)
    (hshape : S = C ν * X ^ b * (r.comp (X ^ ρ)) ^ k) :
    S.roots.toFinset.card ≤ 1 + ρ * f.natDegree := by
  apply h.substituted_companion_root_count hδ hr0 hf ρ hρ hS
  intro z hz
  have heval : ν * z ^ b * (r.eval (z ^ ρ)) ^ k = 0 := by
    simpa [hshape, IsRoot] using hz
  rcases mul_eq_zero.mp heval with hfirst | hpow
  · rcases mul_eq_zero.mp hfirst with hν | hb
    · have : S = 0 := by simp [hshape, hν]
      exact False.elim (hS this)
    · left
      exact eq_zero_of_pow_eq_zero hb
  · right
    exact eq_zero_of_pow_eq_zero hpow

/-- A nonconstant complex polynomial has a root of greatest multiplicity;
the maximum is attained, not merely a supremum bound. -/
theorem exists_max_rootMultiplicity (r : ℂ[X]) (hr : 0 < r.natDegree) :
    ∃ α : ℂ, r.IsRoot α ∧
      ∀ β : ℂ, r.IsRoot β → rootMultiplicity β r ≤ rootMultiplicity α r := by
  classical
  have hrne : r ≠ 0 := ne_zero_of_natDegree_gt hr
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root r (natDegree_pos_iff_degree_pos.mp hr).ne'
  let S := r.roots.toFinset
  have hS : S.Nonempty :=
    ⟨α, Multiset.mem_toFinset.mpr ((mem_roots hrne).mpr hα)⟩
  obtain ⟨β, hβ, hmax⟩ :=
    Finset.exists_max_image S (fun z => rootMultiplicity z r) hS
  refine ⟨β, (mem_roots hrne).mp (Multiset.mem_toFinset.mp hβ), ?_⟩
  intro γ hγ
  exact hmax γ (Multiset.mem_toFinset.mpr ((mem_roots hrne).mpr hγ))

/-- A linear companion contains only one root. The companion equation therefore
forces a nonconstant normalized polynomial to concentrate its entire degree at
one nonzero root. -/
theorem GenComp.exists_full_multiplicity_root
    {δ H W : ℕ} {r f : ℂ[X]} (h : GenComp δ H W r f)
    (hδ : 0 < δ) (hr0 : r.eval 0 = 1) (hr : 0 < r.natDegree)
    (hfdeg : f.natDegree = 1) :
    ∃ α : ℂ, α ≠ 0 ∧ r.IsRoot α ∧ rootMultiplicity α r = r.natDegree := by
  have hrne : r ≠ 0 := ne_zero_of_natDegree_gt hr
  have hfpos : 0 < f.natDegree := by omega
  have hfne : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
  obtain ⟨α, hα, hmax⟩ := exists_max_rootMultiplicity r hr
  have hbound := degree_le_maxMultiplicity_mul_companionDegree r f
    (rootMultiplicity α r) hrne hfne (fun _ hβ => h.isRoot_f hδ hr0 hβ) hmax
  rw [hfdeg, Nat.mul_one] at hbound
  have hreverse : rootMultiplicity α r ≤ r.natDegree := by
    have hd := natDegree_le_of_dvd (pow_rootMultiplicity_dvd r α) hrne
    simpa using hd
  refine ⟨α, ?_, hα, Nat.le_antisymm hreverse hbound⟩
  intro hzero
  subst α
  have : r.eval 0 = 0 := hα
  rw [hr0] at this
  exact one_ne_zero this

end Dixmier.General
