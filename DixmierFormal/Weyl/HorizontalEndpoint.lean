/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalPrime
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal ending endpoint

The maximal `y`-degree of the explicit face is `2e`. Horizontal
homogeneity then locates its support point at `(e,2e)`.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

/-- The explicit horizontal face has maximal `y`-degree `2e`. -/
theorem horizontalFace_y_degree
    (α ν : ℂ) (e : ℕ) (hα : α ≠ 0) (hν : ν ≠ 0)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ e) :
    F.degreeOf 1 = 2 * e := by
  let L : MvPolynomial (Fin 2) ℂ :=
    1 + MvPolynomial.C α * MvPolynomial.X 1
  have hfact : F = MvPolynomial.C ν *
      MvPolynomial.X 0 ^ e * L ^ (2 * e) := by
    rw [hF]
    simp only [pow_zero, pow_one]
    dsimp [L]
    rw [mul_pow, ← pow_mul]
    ring
  have hαreg : α ∈ nonZeroDivisors ℂ := by simpa using hα
  have hνreg : ν ∈ nonZeroDivisors ℂ := by simpa using hν
  have hdegterm : (MvPolynomial.C α * MvPolynomial.X (1 : Fin 2)).degreeOf 1 = 1 := by
    rw [MvPolynomial.degreeOf_C_mul (p := MvPolynomial.X (1 : Fin 2)) 1 α hαreg]
    simp
  have hdegL : L.degreeOf 1 = 1 := by
    dsimp [L]
    rw [add_comm]
    rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (by simp [hdegterm])]
    exact hdegterm
  have hL : L ≠ 0 := by
    intro hz
    simp [hz] at hdegL
  have hX : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ≠ 0 := by simp
  have hXpow : (MvPolynomial.X (0 : Fin 2) ^ e : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
    pow_ne_zero _ hX
  rw [hfact, mul_assoc, MvPolynomial.degreeOf_C_mul 1 ν hνreg,
    MvPolynomial.degreeOf_mul_eq hXpow (pow_ne_zero _ hL),
    MvPolynomial.degreeOf_X_pow_of_ne e (by decide : (1 : Fin 2) ≠ 0),
    MvPolynomial.degreeOf_pow_eq 1 L (2 * e) hL, hdegL]
  omega

/-- The endpoint `(e,2e)` really occurs and has minimal grade on the
horizontal face. This is the precise endpoint demanded by the GGV corner. -/
theorem horizontalFace_ending_endpoint
    (α ν : ℂ) (e : ℕ) (hα : α ≠ 0) (hν : ν ≠ 0)
    (he : 0 < e) (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ e) :
    expo e (2 * e) ∈ F.support ∧
      (∀ d ∈ F.support, grade (expo e (2 * e)) ≤ grade d) := by
  have hdegF : F.degreeOf 1 = 2 * e :=
    horizontalFace_y_degree α ν e hα hν F hF
  have hFne : F ≠ 0 := by
    intro hz
    rw [hz] at hdegF
    simp at hdegF
    omega
  have hsupport : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hFne
  obtain ⟨d, hd, hd1⟩ :=
    Finset.exists_mem_eq_sup F.support hsupport (fun d => d (1 : Fin 2))
  have hdy : d (1 : Fin 2) = 2 * e := by
    rw [← MvPolynomial.degreeOf_eq_sup] at hd1
    exact hd1.symm.trans hdegF
  have hhom : F.IsWeightedHomogeneous (wt 1 0) (e : ℤ) := by
    rw [hF]
    have hRhom := crossingBase_isWeightedHomogeneous α 2 1 0
    convert (hRhom.pow e).C_mul ν using 1 <;> simp [wt]
  have hdweight := hhom (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hj : j = 2 * e := by simpa [expo] using hdy
  rw [expo_weight] at hdweight
  have hi : i = e := by omega
  subst i
  subst j
  constructor
  · simpa only [expo] using hd
  · intro d hd
    obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
    have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
    rw [expo_weight] at hw
    have hy_le : j ≤ 2 * e := by
      have hle := MvPolynomial.le_degreeOf_of_mem_support
        (i := (1 : Fin 2)) hd
      rw [hdegF] at hle
      simpa [expo] using hle
    simp [grade, expo]
    omega

/-- A nonconstant horizontal binomial face is a genuine Newton face. -/
theorem horizontalFace_support_two
    (α ν : ℂ) (e : ℕ) (hα : α ≠ 0) (hν : ν ≠ 0)
    (he : 0 < e) (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ e) :
    1 < F.support.card := by
  have htop := (horizontalFace_ending_endpoint α ν e hα hν he F hF).1
  by_contra hnot
  have hcard : F.support.card ≤ 1 := by omega
  have hone : ∀ d ∈ F.support, d = expo e (2 * e) := by
    intro d hd
    exact (Finset.card_le_one_iff.mp hcard) hd htop
  have hmon := MvPolynomial.eq_monomial_of_support_subset_singleton hone
  let v : Fin 2 → ℂ := ![1, 0]
  have heval : MvPolynomial.eval v F = ν := by
    rw [hF]
    simp [v]
  have hzero : MvPolynomial.eval v F = 0 := by
    rw [hmon]
    simp [MvPolynomial.eval_monomial, v, expo, Fin.prod_univ_two]
    right
    omega
  exact hν (heval.symm.trans hzero)

end Dixmier.Weyl
