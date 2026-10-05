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
# Roots of a general derivative-bracket fixed point

The top-face equation of a homogeneous companion has the form
`A f' g - B f g' = g`. When `B ≠ 0`, every root of `g` is a root of
`f`, with no face-shape or degree assumption.
-/

namespace Dixmier.General
open Polynomial Finset

set_option maxHeartbeats 1000000

theorem derivative_bracket_root_containment
    (f g : ℂ[X]) (A B : ℂ) (hg : g ≠ 0) (hB : B ≠ 0)
    (heq : C A * (derivative f * g) -
      C B * (f * derivative g) = g)
    {z : ℂ} (hz : g.IsRoot z) : f.IsRoot z := by
  have hm : 0 < rootMultiplicity z g :=
    (rootMultiplicity_pos hg).mpr hz
  obtain ⟨u, hgu, hndvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg z
  generalize hmdef : rootMultiplicity z g = m at hgu hm ⊢
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu : u.eval z ≠ 0 := fun h0 =>
    hndvd (dvd_iff_isRoot.mpr h0)
  have hdg : derivative g = (X - C z) ^ k *
      (C ((k : ℂ) + 1) * u + (X - C z) * derivative u) := by
    rw [hgu, derivative_mul, derivative_X_sub_C_pow]
    push_cast
    ring
  have hcancel :
      C A * (derivative f * ((X - C z) * u)) -
        C B * (f *
          (C ((k : ℂ) + 1) * u + (X - C z) * derivative u)) =
        (X - C z) * u := by
    apply mul_left_cancel₀ (pow_ne_zero k (X_sub_C_ne_zero z))
    have h := heq
    rw [hdg, hgu] at h
    linear_combination h
  have hval := congrArg (eval z) hcancel
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X,
    sub_self, zero_mul, mul_zero] at hval
  have hk : ((k : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hprod : B * f.eval z * ((k : ℂ) + 1) * u.eval z = 0 := by
    linear_combination -hval
  have hf : f.eval z = 0 := by
    have := (mul_eq_zero.mp hprod).resolve_right hu
    have := (mul_eq_zero.mp this).resolve_right hk
    exact (mul_eq_zero.mp this).resolve_left hB
  exact hf

/-- Distinct roots of the first top face are bounded by the degree of
the companion's top-face polynomial. -/
theorem derivative_bracket_root_count
    (f g : ℂ[X]) (A B : ℂ) (hg : g ≠ 0) (hB : B ≠ 0)
    (heq : C A * (derivative f * g) -
      C B * (f * derivative g) = g) :
    g.roots.toFinset.card ≤ f.natDegree := by
  classical
  have hf : f ≠ 0 := by
    intro hz
    rw [hz] at heq
    simp at heq
    exact hg heq.symm
  have hsubset : g.roots.toFinset ⊆ f.roots.toFinset := by
    intro z hz
    have hgz : g.IsRoot z :=
      (mem_roots hg).mp (Multiset.mem_toFinset.mp hz)
    have hfz := derivative_bracket_root_containment
      f g A B hg hB heq hgz
    exact Multiset.mem_toFinset.mpr ((mem_roots hf).mpr hfz)
  exact (Finset.card_mono hsubset).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' f))

/-- Above companion degree one, the highest possible derivative term
must cancel. This is the scalar endpoint-parallelism equation. -/
theorem derivative_bracket_top_degree_balance
    (f g : ℂ[X]) (A B : ℂ)
    (hg : 0 < g.natDegree) (hf : 2 ≤ f.natDegree)
    (heq : C A * (derivative f * g) -
      C B * (f * derivative g) = g) :
    A * (f.natDegree : ℂ) = B * (g.natDegree : ℂ) := by
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
  have hc := congrArg (fun p : ℂ[X] => p.coeff ((L - 1) + e)) heq
  rw [coeff_sub, coeff_C_mul, coeff_C_mul, hgf, hfg, hzero, hdg, hdf] at hc
  have hmult : (A * (L : ℂ) - B * (e : ℂ)) *
      (f.coeff L * g.coeff e) = 0 := by
    linear_combination hc
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hmult).resolve_right (mul_ne_zero htopf htopg))

/-- The degree-one boundary genuinely lacks top-degree balance: the
same derivative-bracket equation can hold with `A·deg(f) ≠ B·deg(g)`.
This is a scalar control, not a Weyl counterexample. -/
theorem derivative_bracket_linear_boundary_control :
    C (3 : ℂ) *
        (derivative (X - C 1) * (X - C 1) ^ 2) -
      C (1 : ℂ) *
        ((X - C 1) * derivative ((X - C 1) ^ 2)) =
      (X - C 1) ^ 2 := by
  rw [derivative_X_sub_C_pow, derivative_X_sub_C]
  simp only [map_ofNat, map_one]
  have hC2 : (C (2 : ℂ) : ℂ[X]) = 2 := C_ofNat 2
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, hC2]
  ring

theorem derivative_bracket_linear_boundary_unbalanced :
    (3 : ℂ) * ((X - C 1 : ℂ[X]).natDegree : ℂ) ≠
      (1 : ℂ) * (((X - C 1 : ℂ[X]) ^ 2).natDegree : ℂ) := by
  rw [natDegree_pow, natDegree_X_sub_C]
  norm_num

end Dixmier.General
