/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Defs
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Euler operator and vanishing moments at a repeated root

If `(X - a)^m` divides `S`, the weighted power sums `∑ S_n aⁿ nᵏ` vanish for `k < m`, hence
`∑ S_n aⁿ g(n) = 0` for every polynomial `g` of degree `< m`.  Choosing `g` to vanish on all
but a few support exponents turns this into the sparse-root lemmas.
-/

namespace Dixmier

open Polynomial Finset

section Euler

variable {K : Type*} [Field K]

/-- The Euler operator `p ↦ X * p'`. -/
noncomputable def euler (p : K[X]) : K[X] := X * derivative p

theorem coeff_euler (p : K[X]) (n : ℕ) : (euler p).coeff n = (n : K) * p.coeff n := by
  rcases n with _ | m
  · simp [euler]
  · rw [euler, coeff_X_mul, coeff_derivative]; push_cast; ring

theorem coeff_euler_iterate (p : K[X]) (k n : ℕ) :
    (euler^[k] p).coeff n = (n : K) ^ k * p.coeff n := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coeff_euler, ih, pow_succ]; ring

theorem pow_dvd_euler {a : K} {m : ℕ} {p : K[X]} (h : (X - C a) ^ (m + 1) ∣ p) :
    (X - C a) ^ m ∣ euler p := by
  have hd := pow_sub_one_dvd_derivative_of_pow_dvd h
  rw [Nat.add_sub_cancel] at hd
  exact hd.mul_left X

theorem pow_dvd_euler_iterate {a : K} {m : ℕ} {p : K[X]} (h : (X - C a) ^ m ∣ p) (k : ℕ) :
    (X - C a) ^ (m - k) ∣ euler^[k] p := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases Nat.lt_or_ge k m with hk | hk
    · have hmk : m - k = (m - (k + 1)) + 1 := by omega
      rw [hmk] at ih
      exact pow_dvd_euler ih
    · have hmk : m - (k + 1) = 0 := by omega
      rw [hmk, pow_zero]; exact one_dvd _

/-- Vanishing power sums at a root of multiplicity at least `m`. -/
theorem sum_coeff_pow_mul_eq_zero {S : K[X]} {a : K} {m : ℕ} (h : (X - C a) ^ m ∣ S)
    {k : ℕ} (hk : k < m) : ∑ n ∈ S.support, S.coeff n * a ^ n * (n : K) ^ k = 0 := by
  have hroot : (euler^[k] S).IsRoot a := by
    have hdvd : (X - C a) ∣ euler^[k] S :=
      (dvd_pow_self _ (by omega : m - k ≠ 0)).trans (pow_dvd_euler_iterate h k)
    exact dvd_iff_isRoot.mp hdvd
  have hsupp : (euler^[k] S).support ⊆ S.support := by
    intro n hn
    rw [mem_support_iff, coeff_euler_iterate] at hn
    exact mem_support_iff.mpr (right_ne_zero_of_mul hn)
  rw [IsRoot, eval_eq_sum, Polynomial.sum_def, Finset.sum_subset hsupp] at hroot
  · rw [← hroot]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coeff_euler_iterate]; ring
  · intro n _ hn
    rw [notMem_support_iff.mp hn, zero_mul]

/-- Vanishing moments against every test polynomial of degree `< m`. -/
theorem moment_eq_zero {S g : K[X]} {a : K} {m : ℕ} (h : (X - C a) ^ m ∣ S)
    (hg : g.natDegree < m) : ∑ n ∈ S.support, S.coeff n * a ^ n * g.eval (n : K) = 0 := by
  simp_rw [eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < m := by rw [Finset.mem_range] at hk; omega
  calc ∑ n ∈ S.support, S.coeff n * a ^ n * (g.coeff k * (n : K) ^ k)
      = g.coeff k * ∑ n ∈ S.support, S.coeff n * a ^ n * (n : K) ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    _ = 0 := by rw [sum_coeff_pow_mul_eq_zero h hk', mul_zero]

end Euler

section TestPoly

variable {K : Type*} [Field K]

/-- The test polynomial `∏_{m ∈ T} (X - m)`. -/
noncomputable def testPoly (T : Finset ℕ) : K[X] := ∏ m ∈ T, (X - C (m : K))

theorem natDegree_testPoly_le (T : Finset ℕ) : (testPoly T : K[X]).natDegree ≤ T.card := by
  unfold testPoly
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun (m : ℕ) _ => natDegree_X_sub_C_le ((m : ℕ) : K))).trans ?_
  simp

theorem eval_testPoly (T : Finset ℕ) (n : ℕ) :
    (testPoly T : K[X]).eval (n : K) = ∏ m ∈ T, ((n : K) - m) := by
  simp [testPoly, eval_prod]

theorem eval_testPoly_eq_zero {T : Finset ℕ} {n : ℕ} (hn : n ∈ T) :
    (testPoly T : K[X]).eval (n : K) = 0 := by
  rw [eval_testPoly]; exact Finset.prod_eq_zero hn (sub_self _)

theorem eval_testPoly_ne_zero [CharZero K] {T : Finset ℕ} {n : ℕ} (hn : n ∉ T) :
    (testPoly T : K[X]).eval (n : K) ≠ 0 := by
  rw [eval_testPoly, Finset.prod_ne_zero_iff]
  intro m hm
  rw [sub_ne_zero, Ne, Nat.cast_inj]
  rintro rfl; exact hn hm

end TestPoly

end Dixmier
