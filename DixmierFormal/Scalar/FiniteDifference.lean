/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Defs
public import Mathlib.Algebra.Polynomial.Roots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Rigidity for a polynomial finite difference

The exact homogeneous Weyl calculation in the grade `-1` case leads to a
polynomial shift difference equal to one. This file isolates the scalar
consequence needed for that classification.
-/

namespace Dixmier

open Polynomial

/-- The degree-`k` falling-factorial polynomial with roots `1, …, k`. -/
noncomputable def fallingFactorialPoly {K : Type*} [Field K] (k : ℕ) : K[X] :=
  ∏ i ∈ Finset.range k, (X - C ((i + 1 : ℕ) : K))

theorem fallingFactorialPoly_natDegree {K : Type*} [Field K] (k : ℕ) :
    (fallingFactorialPoly (K := K) k).natDegree = k := by
  simpa [fallingFactorialPoly] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card (Finset.range k)
      (fun i : ℕ => ((i + 1 : ℕ) : K)))

theorem fallingFactorialPoly_ne_zero {K : Type*} [Field K] {k : ℕ} (hk : 0 < k) :
    fallingFactorialPoly (K := K) k ≠ 0 := by
  intro hzero
  have hdeg := fallingFactorialPoly_natDegree (K := K) k
  rw [hzero] at hdeg
  simp at hdeg
  omega

/-- A polynomial whose forward unit difference is one is linear with slope one. -/
theorem polynomial_shift_difference_eq_one_is_linear {K : Type*} [Field K] [CharZero K]
    (F : K[X]) (hF : F.comp (X + C (1 : K)) - F = 1) :
    F = X + C (F.eval 0) := by
  have hstep (n : ℕ) : F.eval ((n : K) + 1) = F.eval (n : K) + 1 := by
    have h := congrArg (fun p : K[X] => p.eval (n : K)) hF
    have hdiff : F.eval ((n : K) + 1) - F.eval (n : K) = 1 := by
      simpa [eval_sub, eval_comp] using h
    calc
      F.eval ((n : K) + 1) = F.eval (n : K) +
          (F.eval ((n : K) + 1) - F.eval (n : K)) := by ring
      _ = F.eval (n : K) + 1 := by rw [hdiff]
  have hvals (n : ℕ) : F.eval (n : K) = F.eval 0 + n := by
    induction n with
    | zero => simp
    | succ n hn =>
        rw [Nat.cast_succ, hstep n, hn]
        ring
  have hinj : Function.Injective (fun n : ℕ => (n : K)) := by
    intro m n h
    exact Nat.cast_injective h
  have hrange : Set.Infinite (Set.range fun n : ℕ => (n : K)) :=
    Set.infinite_range_of_injective hinj
  have hsubset : Set.range (fun n : ℕ => (n : K)) ⊆
      {x : K | F.eval x = (X + C (F.eval 0)).eval x} := by
    rintro x ⟨n, rfl⟩
    change F.eval (n : K) = (X + C (F.eval 0)).eval (n : K)
    rw [hvals]
    simp only [eval_add, eval_X, eval_C]
    ring
  have hInfinite : Set.Infinite
      {x : K | F.eval x = (X + C (F.eval 0)).eval x} := hrange.mono hsubset
  exact Polynomial.eq_of_infinite_eval_eq F (X + C (F.eval 0)) hInfinite

/-- The same finite-difference hypothesis determines the degree exactly. -/
theorem natDegree_eq_one_of_shift_difference_eq_one {K : Type*} [Field K] [CharZero K]
    (F : K[X]) (hF : F.comp (X + C (1 : K)) - F = 1) : F.natDegree = 1 := by
  rw [polynomial_shift_difference_eq_one_is_linear F hF]
  exact natDegree_X_add_C _

/-- A nonzero step size does not change the degree consequence of a constant polynomial
finite difference. Rescaling the variable reduces the step to one. -/
theorem natDegree_eq_one_of_shift_difference_eq_one_step
    {K : Type*} [Field K] [CharZero K] (F : K[X]) (a : K) (ha : a ≠ 0)
    (hF : F.comp (X + C a) - F = 1) : F.natDegree = 1 := by
  let G : K[X] := F.comp (X * C a)
  have hscaled : (F.comp (X + C a)).comp (X * C a) - F.comp (X * C a) = 1 := by
    have hh := congrArg (fun H : K[X] => H.comp (X * C a)) hF
    simpa only [Polynomial.sub_comp, one_comp] using hh
  have hinner : (X * C a).comp (X + C (1 : K)) =
      (X + C a).comp (X * C a) := by
    ext x
    simp [mul_add]
  have hG : G.comp (X + C (1 : K)) - G = 1 := by
    change (F.comp (X * C a)).comp (X + C (1 : K)) -
      F.comp (X * C a) = 1
    rw [Polynomial.comp_assoc, hinner]
    rw [← Polynomial.comp_assoc]
    exact hscaled
  have hGdeg : G.natDegree = 1 :=
    natDegree_eq_one_of_shift_difference_eq_one G hG
  have hGdeg' : G.natDegree = F.natDegree := by
    dsimp [G]
    rw [natDegree_comp, show X * C a = C a * X by ring,
      natDegree_C_mul_X a ha, Nat.mul_one]
  omega

/-- The reverse difference `F(X) - F(X + a) = 1` has the same degree consequence. -/
theorem natDegree_eq_one_of_reverse_shift_difference_eq_one_step
    {K : Type*} [Field K] [CharZero K] (F : K[X]) (a : K) (ha : a ≠ 0)
    (hF : F - F.comp (X + C a) = 1) : F.natDegree = 1 := by
  have hneg : (-F).comp (X + C a) - (-F) = 1 := by
    simpa only [Polynomial.neg_comp, neg_sub_neg] using hF
  have hdeg := natDegree_eq_one_of_shift_difference_eq_one_step (-F) a ha hneg
  simpa using hdeg

/-- If a positive-step finite difference of a product is one, and one factor already
has degree `k > 0`, then that factor exhausts the degree: the other two factors are
constant and `k = 1`. This is the terminal degree inference in the homogeneous-pair
reduction; the Weyl-algebra argument must still produce the displayed polynomial identity. -/
theorem product_reverse_shift_difference_forces_unit_factor_degree
    {K : Type*} [Field K] [CharZero K] (f A g : K[X]) (k : ℕ) (hk : 0 < k)
    (hf : f ≠ 0) (hA : A ≠ 0) (hg : g ≠ 0) (hAdeg : A.natDegree = k)
    (h : f * A * g - (f * A * g).comp (X + C (k : K)) = 1) :
    f.natDegree = 0 ∧ k = 1 ∧ g.natDegree = 0 := by
  have hstep : (k : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hdegree := natDegree_eq_one_of_reverse_shift_difference_eq_one_step
    (f * A * g) (k : K) hstep h
  have hmul : (f * A * g).natDegree =
      f.natDegree + A.natDegree + g.natDegree := by
    rw [natDegree_mul (mul_ne_zero hf hA) hg, natDegree_mul hf hA]
  rw [hmul, hAdeg] at hdegree
  omega

/-- The exact falling-factorial middle factor in the homogeneous Weyl-pair reduction is
nonconstant of degree `k`, so the preceding degree argument forces `k = 1`. -/
theorem fallingFactorial_shift_difference_forces_generator_case
    {K : Type*} [Field K] [CharZero K] (f g : K[X]) (k : ℕ) (hk : 0 < k)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (h : f * fallingFactorialPoly (K := K) k * g -
      (f * fallingFactorialPoly (K := K) k * g).comp (X + C (k : K)) = 1) :
    f.natDegree = 0 ∧ k = 1 ∧ g.natDegree = 0 := by
  exact product_reverse_shift_difference_forces_unit_factor_degree f
    (fallingFactorialPoly (K := K) k) g k hk hf
    (fallingFactorialPoly_ne_zero hk)
    hg (fallingFactorialPoly_natDegree k) h

/-- If the unit shift difference of `X * f(X) * g(X + 1)` is one, both factors are
constant. This is the degree step in the proposed grade `-1` homogeneous-pair reduction. -/
theorem shiftProduct_eq_one_forces_constant_factors {K : Type*} [Field K] [CharZero K]
    (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ((X * f * g.comp (X + C (1 : K))).comp (X + C (1 : K))) -
      (X * f * g.comp (X + C (1 : K))) = 1) :
    f.natDegree = 0 ∧ g.natDegree = 0 := by
  let H : K[X] := X * f * g.comp (X + C (1 : K))
  have hH : H.comp (X + C (1 : K)) - H = 1 := by simpa [H] using h
  have hdeg : H.natDegree = 1 := natDegree_eq_one_of_shift_difference_eq_one H hH
  have hshiftdeg : (g.comp (X + C (1 : K))).natDegree = g.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, Nat.mul_one]
  have hshiftne : g.comp (X + C (1 : K)) ≠ 0 := by
    intro hz
    have hzero := (comp_eq_zero_iff (p := g) (q := X + C (1 : K))).mp hz
    rcases hzero with hg0 | ⟨_, hconst⟩
    · exact hg hg0
    · have hdegconst := congrArg natDegree hconst
      rw [natDegree_X_add_C, natDegree_C] at hdegconst
      omega
  have hinner : (X * f).natDegree = 1 + f.natDegree := by
    rw [natDegree_mul X_ne_zero hf, natDegree_X]
  have houter : ((X * f) * g.comp (X + C (1 : K))).natDegree =
      (X * f).natDegree + (g.comp (X + C (1 : K))).natDegree :=
    natDegree_mul (mul_ne_zero X_ne_zero hf) hshiftne
  have hproddeg : H.natDegree = 1 + f.natDegree + g.natDegree := by
    change ((X * f) * g.comp (X + C (1 : K))).natDegree = _
    rw [houter, hinner, hshiftdeg]
  constructor <;> omega

end Dixmier
