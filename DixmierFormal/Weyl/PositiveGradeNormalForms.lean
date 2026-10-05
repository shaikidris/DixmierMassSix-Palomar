/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GradeNormalForms

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Normal forms for arbitrary nonnegative Weyl grades

An operator supported on grade `j ≥ 0` has the form `p(YX) X^j`. The
construction is an explicit triangular change of basis from PBW monomials.
-/

namespace Dixmier.Weyl

open Polynomial

variable {K : Type*} [Field K]

noncomputable def upperShiftPolyOf (j : ℕ) : ℕ → K[X]
  | 0 => 1
  | i + 1 => upperShiftPolyOf j i * (X - C ((i + j + 1 : ℕ) : K))

private theorem xPowApplyOf (n : ℕ) : ∀ p : K[X], (xOp K ^ n) p = X ^ n * p := by
  induction n with
  | zero => intro p; simp [xOp]
  | succ n ih =>
      intro p
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [xOp, LinearMap.mulLeft_apply, pow_succ, mul_assoc]

private theorem y_mul_xpow_succ_of (i : ℕ) :
    yOp K * xOp K ^ (i + 1) =
      xOp K ^ (i + 1) * yOp K + ((i + 1 : K) • xOp K ^ i) := by
  refine LinearMap.ext fun p => ?_
  change yOp K ((xOp K ^ (i + 1)) p) =
    (xOp K ^ (i + 1)) (yOp K p) + ((i + 1 : K) • ((xOp K ^ i) p))
  rw [xPowApplyOf (K := K) (i + 1) p, xPowApplyOf (K := K) (i + 1) (yOp K p),
    xPowApplyOf (K := K) i p]
  change derivative (X ^ (i + 1) * p) =
    X ^ (i + 1) * derivative p + ((i + 1 : K) • (X ^ i * p))
  rw [derivative_mul, derivative_X_pow_succ]
  simp [Polynomial.smul_eq_C_mul, mul_assoc]
  ring

/-- The basic generator commutator with a positive power of `X`. -/
theorem yOp_mul_xOp_pow_succ (i : ℕ) :
    yOp K * xOp K ^ (i + 1) =
      xOp K ^ (i + 1) * yOp K + ((i + 1 : K) • xOp K ^ i) :=
  y_mul_xpow_succ_of (K := K) i

private theorem poly_eval_commute_of (S : Module.End K K[X]) (p : K[X]) :
    aeval S p * S = S * aeval S p := by
  calc
    aeval S p * S = aeval S p * aeval S X := by rw [aeval_X]
    _ = aeval S (p * X) := (map_mul _ _ _).symm
    _ = aeval S (X * p) := by rw [mul_comm p X]
    _ = aeval S X * aeval S p := map_mul _ _ _
    _ = S * aeval S p := by rw [aeval_X]

private theorem euler_shift_pbw_of (n i : ℕ) :
    (yOp K * xOp K -
        algebraMap K (Module.End K K[X]) ((n + 1 : ℕ) : K)) *
        (xOp K ^ n * yOp K ^ i) =
      xOp K ^ (n + 1) * yOp K ^ (i + 1) := by
  let c : Module.End K K[X] :=
    algebraMap K (Module.End K K[X]) ((n + 1 : ℕ) : K)
  have hmul := y_mul_xpow_succ_of (K := K) n
  have hc : c * (xOp K ^ n * yOp K ^ i) =
      ((n + 1 : K) • (xOp K ^ n * yOp K ^ i)) := by
    dsimp [c]
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hsmul : ((n + 1 : K) • xOp K ^ n) * yOp K ^ i =
      ((n + 1 : K) • (xOp K ^ n * yOp K ^ i)) := smul_mul_assoc _ _ _
  have hy : yOp K * yOp K ^ i = yOp K ^ (i + 1) := by
    rw [← pow_succ']
  calc
    (yOp K * xOp K - c) * (xOp K ^ n * yOp K ^ i) =
        (yOp K * xOp K ^ (n + 1)) * yOp K ^ i -
          c * (xOp K ^ n * yOp K ^ i) := by
      rw [sub_mul]
      congr 1
      · calc
          (yOp K * xOp K) * (xOp K ^ n * yOp K ^ i) =
              yOp K * (xOp K * (xOp K ^ n * yOp K ^ i)) :=
            mul_assoc _ _ _
          _ = yOp K * ((xOp K * xOp K ^ n) * yOp K ^ i) :=
            congrArg (fun z : Module.End K K[X] => yOp K * z)
              (mul_assoc (xOp K) (xOp K ^ n) (yOp K ^ i)).symm
          _ = yOp K * (xOp K ^ (n + 1) * yOp K ^ i) := by
            rw [← pow_succ' (xOp K) n]
          _ = (yOp K * xOp K ^ (n + 1)) * yOp K ^ i :=
            (mul_assoc (yOp K) (xOp K ^ (n + 1)) (yOp K ^ i)).symm
    _ = (xOp K ^ (n + 1) * yOp K +
          ((n + 1 : K) • xOp K ^ n)) * yOp K ^ i -
          c * (xOp K ^ n * yOp K ^ i) := by rw [hmul]
    _ = (xOp K ^ (n + 1) * yOp K) * yOp K ^ i := by
      rw [add_mul, hsmul, hc]
      simp
    _ = xOp K ^ (n + 1) * yOp K ^ (i + 1) := by
      calc
        (xOp K ^ (n + 1) * yOp K) * yOp K ^ i =
            xOp K ^ (n + 1) * (yOp K * yOp K ^ i) := by simp [mul_assoc]
        _ = xOp K ^ (n + 1) * yOp K ^ (i + 1) := by rw [hy]

private theorem upperShiftOf_basis (j i : ℕ) :
    aeval (yOp K * xOp K) (upperShiftPolyOf (K := K) j i) * xOp K ^ j =
      xOp K ^ (i + j) * yOp K ^ i := by
  induction i with
  | zero => simp [upperShiftPolyOf]
  | succ i ih =>
      let S : Module.End K K[X] := yOp K * xOp K
      let A : Module.End K K[X] := aeval S (upperShiftPolyOf (K := K) j i)
      let c : Module.End K K[X] :=
        algebraMap K (Module.End K K[X]) ((i + j + 1 : ℕ) : K)
      change aeval S
          (upperShiftPolyOf (K := K) j i * (X - C ((i + j + 1 : ℕ) : K))) *
          xOp K ^ j = _
      rw [map_mul]
      have heval : aeval S (X - C ((i + j + 1 : ℕ) : K)) = S - c := by
        simp [S, c]
      rw [heval]
      have hAS : A * S = S * A := by
        dsimp [A]
        exact poly_eval_commute_of S (upperShiftPolyOf (K := K) j i)
      have hAc : A * c = c * A := (Algebra.commutes _ _).symm
      have hshift : A * (S - c) = (S - c) * A := by
        calc
          A * (S - c) = A * S - A * c := mul_sub _ _ _
          _ = S * A - c * A := by rw [hAS, hAc]
          _ = (S - c) * A := (sub_mul _ _ _).symm
      calc
        (A * (S - c)) * xOp K ^ j = ((S - c) * A) * xOp K ^ j := by rw [hshift]
        _ = (S - c) * (A * xOp K ^ j) := by simp [mul_assoc]
        _ = (S - c) * (xOp K ^ (i + j) * yOp K ^ i) := by rw [ih]
        _ = xOp K ^ (i + j + 1) * yOp K ^ (i + 1) := by
          simpa [S, c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            euler_shift_pbw_of (K := K) (i + j) i
        _ = xOp K ^ (i + 1 + j) * yOp K ^ (i + 1) := by
          congr 2
          all_goals omega

private theorem grade_expo_of (i j : ℕ) :
    grade (expo i j) = (i : ℤ) - j := by
  simp [grade, expo]

private theorem pbw_support_grade_nat_of [CharZero K] (T : A1 K) (j : ℕ)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support,
      grade d = (j : ℤ))
    (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    ∀ p ∈ c.support, p.1 = p.2 + j := by
  intro p hp
  obtain ⟨i, k⟩ := p
  have hcoeff : pbwCoeff (T : Module.End K K[X]) i k = c (i, k) := by
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i k
  have hnonzero : pbwCoeff (T : Module.End K K[X]) i k ≠ 0 := by
    rw [hcoeff]
    exact Finsupp.mem_support_iff.mp hp
  have hs : expo i k ∈ (symbol (T : Module.End K K[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hnonzero
  have h := hgrade (expo i k) hs
  rw [grade_expo_of] at h
  omega

private theorem upperShiftOf_form_sum (j : ℕ) (c : (ℕ × ℕ) →₀ K) :
    aeval (yOp K * xOp K)
      (c.sum (fun p a => a • upperShiftPolyOf (K := K) j p.2)) * xOp K ^ j =
      c.sum (fun p a => a •
        (aeval (yOp K * xOp K) (upperShiftPolyOf (K := K) j p.2) * xOp K ^ j)) := by
  classical
  rw [Finsupp.sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_assoc]

/-- Any operator supported in one nonnegative grade `j` has the form
`p(YX) X^j`. In particular, this supplies the arbitrary positive-grade
normal form required by the source case `(a.2)`. -/
theorem grade_nat_representation [CharZero K] (T : A1 K) (j : ℕ)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support,
      grade d = (j : ℤ)) :
    ∃ g : K[X], (T : Module.End K K[X]) =
      aeval (yOp K * xOp K) g * xOp K ^ j := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  refine ⟨c.sum (fun p a => a • upperShiftPolyOf (K := K) j p.2), ?_⟩
  rw [upperShiftOf_form_sum]
  rw [Finsupp.sum] at hc ⊢
  rw [← hc]
  apply Finset.sum_congr rfl
  intro p hp
  have hrel := pbw_support_grade_nat_of (T := T) j hgrade c hc p hp
  change c p • (xOp K ^ p.1 * yOp K ^ p.2) =
    c p • (aeval (yOp K * xOp K)
      (upperShiftPolyOf (K := K) j p.2) * xOp K ^ j)
  rw [hrel, ← upperShiftOf_basis]

end Dixmier.Weyl
