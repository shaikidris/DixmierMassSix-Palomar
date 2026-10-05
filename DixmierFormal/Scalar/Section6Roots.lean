/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Section6Controls

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

theorem section6_cube_roots_card :
    (X^3 - 1 : ℂ[X]).roots.toFinset.card = 3 := by
  have hsep : (X^3 - 1 : ℂ[X]).Separable := by
    rw [X_pow_sub_one_separable_iff]
    norm_num
  have hnodup := nodup_roots hsep
  rw [Multiset.toFinset_card_of_nodup hnodup]
  rw [IsAlgClosed.card_roots_eq_natDegree]
  simpa only [map_one] using (natDegree_X_pow_sub_C (R := ℂ) (n := 3) (r := 1))

theorem section6_imprimitive_fourfold (a : ℂ)
    (ha : a ∈ (X^3 - 1 : ℂ[X]).roots.toFinset) :
    (X - C a)^4 ∣ ((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2 := by
  have hroot : (X^3 - 1 : ℂ[X]).IsRoot a := by
    have hne : (X^3 - 1 : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
    exact (mem_roots hne).mp (Multiset.mem_toFinset.mp ha)
  have hdvd : X - C a ∣ (1-X^3 : ℂ[X]) := by
    have h := (dvd_iff_isRoot).mpr hroot
    convert dvd_neg.mpr h using 1 <;> ring
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hdvd 4) _
end Dixmier
namespace Dixmier
open Polynomial
theorem section6_rootMultiplicity_pow (p : ℂ[X]) (a : ℂ) (n : ℕ) :
    rootMultiplicity a (p^n) = n * rootMultiplicity a p := by
  classical
  rw [← count_roots, roots_pow, Multiset.count_nsmul, count_roots]

theorem section6_imprimitive_exact_fourfold (a : ℂ)
    (ha : a ∈ (X^3 - 1 : ℂ[X]).roots.toFinset) :
    rootMultiplicity a (((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2) = 4 := by
  have hroot : (X^3 - 1 : ℂ[X]).IsRoot a := by
    have hne : (X^3 - 1 : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
    exact (mem_roots hne).mp (Multiset.mem_toFinset.mp ha)
  have ha3 : a^3 = 1 := by
    have := hroot.eq_zero
    exact sub_eq_zero.mp (by simpa [eval_sub, eval_pow] using this)
  have hbase : (X^3 - 1 : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
  have hpsep : (X^3 - 1 : ℂ[X]).Separable := by
    rw [X_pow_sub_one_separable_iff]
    norm_num
  have hp1 : rootMultiplicity a (X^3 - 1 : ℂ[X]) = 1 := by
    apply Nat.le_antisymm (rootMultiplicity_le_one_of_separable hpsep a)
    exact (Nat.succ_le_iff.mpr ((rootMultiplicity_pos hbase).mpr hroot))
  have hp : rootMultiplicity a (1-X^3 : ℂ[X]) = 1 := by
    rw [show (1-X^3 : ℂ[X]) = -(X^3-1) by ring]
    rw [← count_roots, roots_neg, count_roots]
    exact hp1
  have hq : rootMultiplicity a (1+2*X^3 : ℂ[X]) = 0 := by
    apply rootMultiplicity_eq_zero
    rw [IsRoot, eval_add, eval_mul, eval_pow]
    norm_num [ha3]
  have hnonzero : ((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2 ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero <;> intro h
    · apply hbase
      calc
        X^3 - 1 = -(1-X^3 : ℂ[X]) := by ring
        _ = 0 := by rw [h]; simp
    · have hc := congrArg (fun p : ℂ[X] => p.coeff 0) h
      norm_num at hc
  rw [rootMultiplicity_mul hnonzero, section6_rootMultiplicity_pow,
    section6_rootMultiplicity_pow, hp, hq]

/-- The second cubic factor is squarefree; every one of its roots has
multiplicity at most one. -/
theorem section6_second_factor_rootMultiplicity_le_one (a : ℂ) :
    rootMultiplicity a (1 + 2 * X^3 : ℂ[X]) ≤ 1 := by
  have hsep : (X^3 - C (-1/2 : ℂ) : ℂ[X]).Separable :=
    separable_X_pow_sub_C (-1/2 : ℂ) (by norm_num) (by norm_num)
  have hshape : (1 + 2 * X^3 : ℂ[X]) =
      C (2 : ℂ) * (X^3 - C (-1/2 : ℂ)) := by
        simp only [mul_sub, ← map_mul]
        norm_num
        have hC2 : (C (2 : ℂ) : ℂ[X]) = 2 := by
          calc
            C (2 : ℂ) = C (1 + 1 : ℂ) := by norm_num
            _ = C (1 : ℂ) + C (1 : ℂ) := map_add C 1 1
            _ = 2 := by simp; ring
        rw [hC2]
        ring
  rw [hshape, ← count_roots, roots_C_mul _ (by norm_num), count_roots]
  exact rootMultiplicity_le_one_of_separable hsep a

/-- Any root of multiplicity at least four in the imprimitive control
must be a cube root of unity. Combined with the previous theorems, these
are exactly its three fourth-order roots. -/
theorem section6_imprimitive_fourfold_only_at_cube_roots (a : ℂ)
    (hfour : 4 ≤ rootMultiplicity a (((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2)) :
    a ∈ (X^3 - 1 : ℂ[X]).roots.toFinset := by
  by_contra hnot
  have hbase : (X^3 - 1 : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
  have hrootnot : ¬ (X^3 - 1 : ℂ[X]).IsRoot a := by
    intro hr
    exact hnot (Multiset.mem_toFinset.mpr ((mem_roots hbase).mpr hr))
  have hp : rootMultiplicity a (1-X^3 : ℂ[X]) = 0 := by
    rw [show (1-X^3 : ℂ[X]) = -(X^3-1) by ring]
    rw [← count_roots, roots_neg, count_roots]
    apply rootMultiplicity_eq_zero
    exact hrootnot
  have hnonzero : ((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2 ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero <;> intro h
    · apply hbase
      calc
        X^3 - 1 = -(1-X^3 : ℂ[X]) := by ring
        _ = 0 := by rw [h]; simp
    · have hc := congrArg (fun p : ℂ[X] => p.coeff 0) h
      norm_num at hc
  have hq := section6_second_factor_rootMultiplicity_le_one a
  rw [rootMultiplicity_mul hnonzero, section6_rootMultiplicity_pow,
    section6_rootMultiplicity_pow, hp] at hfour
  omega

end Dixmier
