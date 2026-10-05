/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Validation
public import DixmierFormal.Scalar.FiniteDifference

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Polynomial shifts in the Weyl algebra

If an element `u` intertwines `s` with a scalar translate of `s`, then the same
translation rule holds for every polynomial in `s`.  The Weyl generators give
the shifts by `+1` and `-1` for `s = YX`.
-/

namespace Dixmier.Weyl

open Polynomial

section Intertwining

variable {K R : Type*} [Field K] [Ring R] [Algebra K R]

/-- Polynomial functional calculus preserves a scalar-shift intertwining relation. -/
theorem polynomial_aeval_intertwining (s u c : R)
    (h : u * s = (s + c) * u) (p : K[X]) :
    u * aeval s p = aeval (s + c) p * u := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [aeval_C, aeval_C]
      exact (Algebra.commutes a u).symm
  | add p q hp hq =>
      simp only [map_add]
      rw [mul_add, add_mul, hp, hq]
  | monomial n a ih =>
      have ih' : u * (algebraMap K R a * s ^ n) =
          algebraMap K R a * (s + c) ^ n * u := by
        simpa only [map_mul, aeval_C, map_pow, aeval_X] using ih
      simp only [map_mul, aeval_C, map_pow, aeval_X]
      calc
        u * (algebraMap K R a * s ^ (n + 1)) =
            (u * (algebraMap K R a * s ^ n)) * s := by
          rw [pow_succ]
          simp [mul_assoc]
        _ = (algebraMap K R a * (s + c) ^ n * u) * s := by
          rw [ih']
        _ = algebraMap K R a * (s + c) ^ n * (u * s) := by
          simp [mul_assoc]
        _ = algebraMap K R a * (s + c) ^ n * ((s + c) * u) := by rw [h]
        _ = algebraMap K R a *
            ((s + c) ^ n * (s + c)) * u := by
          simp [mul_assoc]
        _ = algebraMap K R a * (s + c) ^ (n + 1) * u := by
          exact congrArg (fun z : R => algebraMap K R a * z * u)
            (pow_succ (s + c) n).symm

/-- Polynomial composition by `X + 1` evaluates at the correspondingly shifted element. -/
private theorem aeval_comp_add_one (s : R) (p : K[X]) :
    aeval s (p.comp (X + C (1 : K))) = aeval (s + 1) p := by
  rw [aeval_comp]
  simp

/-- Polynomial composition by `X - 1` evaluates at the correspondingly shifted element. -/
private theorem aeval_comp_sub_one (s : R) (p : K[X]) :
    aeval s (p.comp (X - C (1 : K))) = aeval (s - 1) p := by
  rw [aeval_comp]
  simp

/-- Two polynomials evaluated at the same element commute. -/
private theorem aeval_values_commute (s : R) (p q : K[X]) :
    aeval s p * aeval s q = aeval s q * aeval s p := by
  calc
    aeval s p * aeval s q = aeval s (p * q) := (map_mul _ _ _).symm
    _ = aeval s (q * p) := by rw [mul_comm p q]
    _ = aeval s q * aeval s p := map_mul _ _ _

end Intertwining

section WeylShifts

variable {K : Type*} [Field K]

private theorem yx_eq_xy_add_one :
    yOp K * xOp K = xOp K * yOp K + 1 := by
  have h := yOp_mul_xOp_sub_xOp_mul_yOp (K := K)
  calc
    yOp K * xOp K =
        (yOp K * xOp K - xOp K * yOp K) + xOp K * yOp K :=
      (sub_add_cancel _ _).symm
    _ = 1 + xOp K * yOp K := by rw [h]
    _ = xOp K * yOp K + 1 := add_comm _ _

/-- `Y` shifts polynomial functions of `YX` forward by one. -/
theorem yOp_aeval_yx_shift (p : K[X]) :
    yOp K * aeval (yOp K * xOp K) p =
      aeval (yOp K * xOp K + 1) p * yOp K := by
  let S : Module.End K K[X] := yOp K * xOp K
  have h : yOp K * S = (S + 1) * yOp K := by
    dsimp [S]
    calc
      yOp K * (yOp K * xOp K) =
          yOp K * (xOp K * yOp K + 1) := by rw [yx_eq_xy_add_one]
      _ = yOp K * xOp K * yOp K + yOp K := by simp [mul_add, mul_assoc]
      _ = (yOp K * xOp K + 1) * yOp K := by simp [add_mul, mul_assoc]
  have hresult := polynomial_aeval_intertwining
    (K := K) (R := Module.End K K[X]) S (yOp K) (1 : Module.End K K[X]) h p
  simpa only [S] using hresult

/-- `X` shifts polynomial functions of `YX` backward by one. -/
theorem xOp_aeval_yx_shift (p : K[X]) :
    xOp K * aeval (yOp K * xOp K) p =
      aeval (yOp K * xOp K - 1) p * xOp K := by
  let S : Module.End K K[X] := yOp K * xOp K
  have hXY : xOp K * yOp K = yOp K * xOp K - 1 := by
    rw [yx_eq_xy_add_one]
    simp
  have h : xOp K * S = (S - 1) * xOp K := by
    dsimp [S]
    calc
      xOp K * (yOp K * xOp K) = (xOp K * yOp K) * xOp K := by
        simp [mul_assoc]
      _ = (yOp K * xOp K - 1) * xOp K := by rw [hXY]
  have hshift : xOp K * S = (S + (-1 : Module.End K K[X])) * xOp K := by
    calc
      xOp K * S = (S - 1) * xOp K := h
      _ = (S + (-1 : Module.End K K[X])) * xOp K := by rfl
  have hresult := polynomial_aeval_intertwining
    (K := K) (R := Module.End K K[X]) S (xOp K) (-1 : Module.End K K[X]) hshift p
  have harg : S + (-1 : Module.End K K[X]) = S - 1 := by rfl
  rw [harg] at hresult
  simpa only [S] using hresult

/-- Ordered multiplication of a grade `-1` and grade `+1` normal form.
This is the `QP` half of the exact commutator calculation. -/
theorem yx_normal_form_QP (f g : K[X]) :
    ((aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K)) =
      aeval (yOp K * xOp K)
        (X * f * g.comp (X + C (1 : K))) := by
  let S : Module.End K K[X] := yOp K * xOp K
  let gp : K[X] := g.comp (X + C (1 : K))
  change ((aeval S f * yOp K) * (aeval S g * xOp K)) =
    aeval S (X * f * gp)
  have hgp : aeval S gp = aeval (S + 1) g := aeval_comp_add_one S g
  have hEval : aeval S f * aeval S gp * S = aeval S ((f * gp) * X) := by
    simpa only [map_mul, aeval_X, mul_assoc] using
      (map_mul (aeval S) (f * gp) X).symm
  have hpoly : (f * gp) * X = X * f * gp := by
    calc
      (f * gp) * X = X * (f * gp) := mul_comm _ _
      _ = X * f * gp := by rw [← mul_assoc]
  calc
    (aeval S f * yOp K) * (aeval S g * xOp K) =
        (aeval S f * (yOp K * aeval S g)) * xOp K := by
      simp only [mul_assoc]
    _ = (aeval S f * (aeval (S + 1) g * yOp K)) * xOp K := by
      rw [yOp_aeval_yx_shift]
    _ = (aeval S f * aeval (S + 1) g) * S := by
      dsimp [S]
      simp only [mul_assoc]
    _ = aeval S f * aeval S gp * S := by rw [← hgp]
    _ = aeval S ((f * gp) * X) := hEval
    _ = aeval S (X * f * gp) := congrArg (aeval S) hpoly

/-- Ordered multiplication in the reverse order of the same grade `-1` and grade `+1`
normal forms. This is the `PQ` half of the exact commutator calculation. -/
theorem yx_normal_form_PQ (f g : K[X]) :
    ((aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K)) =
      aeval (yOp K * xOp K)
        ((X - C (1 : K)) * f.comp (X - C (1 : K)) * g) := by
  let S : Module.End K K[X] := yOp K * xOp K
  let fm : K[X] := f.comp (X - C (1 : K))
  let xm : K[X] := X - C (1 : K)
  change ((aeval S g * xOp K) * (aeval S f * yOp K)) =
    aeval S (xm * fm * g)
  have hfm : aeval S fm = aeval (S - 1) f := aeval_comp_sub_one S f
  have hxmeval : aeval S xm = S - 1 := by simp [xm]
  have hxy : xOp K * yOp K = S - 1 := by
    have hXY : xOp K * yOp K = yOp K * xOp K - 1 := by
      rw [yx_eq_xy_add_one]
      simp
    simpa [S] using hXY
  have hEval : aeval S g * aeval S fm * aeval S xm =
      aeval S ((g * fm) * xm) := by
    simpa only [map_mul, mul_assoc] using
      (map_mul (aeval S) (g * fm) xm).symm
  have hpoly : (g * fm) * xm = xm * fm * g := by
    calc
      (g * fm) * xm = xm * (g * fm) := mul_comm _ _
      _ = xm * (fm * g) := by rw [mul_comm g fm]
      _ = xm * fm * g := by rw [← mul_assoc]
  calc
    (aeval S g * xOp K) * (aeval S f * yOp K) =
        (aeval S g * (xOp K * aeval S f)) * yOp K := by
      simp only [mul_assoc]
    _ = (aeval S g * (aeval (S - 1) f * xOp K)) * yOp K := by
      rw [xOp_aeval_yx_shift]
    _ = (aeval S g * aeval (S - 1) f) * (xOp K * yOp K) := by
      simp only [mul_assoc]
    _ = aeval S g * aeval S fm * (S - 1) := by
      rw [← hfm, hxy]
    _ = aeval S g * aeval S fm * aeval S xm := by rw [← hxmeval]
    _ = aeval S ((g * fm) * xm) := hEval
    _ = aeval S (xm * fm * g) := congrArg (aeval S) hpoly

/-- Exact commutator for the grade `-1` and grade `+1` polynomial normal forms.
The representation theorem for arbitrary operators of these grades and the
extraction of the resulting scalar polynomial equation are proved below. -/
theorem yx_normal_form_commutator (f g : K[X]) :
    ((aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K) -
      (aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K)) =
      aeval (yOp K * xOp K)
        (X * f * g.comp (X + C (1 : K)) -
          (X - C (1 : K)) * f.comp (X - C (1 : K)) * g) := by
  rw [yx_normal_form_QP, yx_normal_form_PQ, ← aeval_sub]

end WeylShifts

section PolynomialEvaluation

variable {K : Type*} [Field K]

private theorem yx_apply_Xpow (n : ℕ) :
    (yOp K * xOp K) (X ^ n) = ((n + 1 : K) • X ^ n) := by
  change yOp K (xOp K (X ^ n)) = ((n + 1 : K) • X ^ n)
  have hx : xOp K (X ^ n) = X ^ (n + 1) := by
    simp [xOp, LinearMap.mulLeft_apply, pow_succ']
  rw [hx]
  simp [yOp, derivative_X_pow_succ, Polynomial.smul_eq_C_mul]

private theorem pow_apply_eigen (S : Module.End K K[X]) (v : K[X]) (c : K)
    (hS : S v = c • v) (k : ℕ) : (S ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hS, smul_smul, pow_succ]

private theorem aeval_apply_eigen (S : Module.End K K[X]) (v : K[X]) (c : K)
    (hS : S v = c • v) (p : K[X]) :
    (aeval S p) v = p.eval c • v := by
  have hpow := fun k => pow_apply_eigen S v c hS k
  induction p using Polynomial.induction_on with
  | C a =>
      simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, eval_add, hp, hq, add_smul]
  | monomial n a ih =>
      simp only [map_mul, map_pow, aeval_C, aeval_X, eval_mul, eval_C, eval_pow]
      rw [Module.End.mul_apply, hpow (n + 1)]
      rw [Algebra.algebraMap_eq_smul_one]
      simp [smul_smul, mul_comm]

private theorem aeval_yx_apply_Xpow (p : K[X]) (n : ℕ) :
    (aeval (yOp K * xOp K) p) (X ^ n) = p.eval (n + 1 : K) • X ^ n := by
  exact aeval_apply_eigen (yOp K * xOp K) (X ^ n) (n + 1 : K)
    (yx_apply_Xpow n) p

/-- Polynomial evaluation at the Euler operator `YX` is injective over a
characteristic-zero field. The monomials `X^n` are eigenvectors with distinct
eigenvalues `n + 1`, so a polynomial in `YX` that vanishes as an operator has
infinitely many roots. -/
theorem aeval_yx_injective [CharZero K] :
    Function.Injective (aeval (yOp K * xOp K) : K[X] →ₐ[K] Module.End K K[X]) := by
  intro p q hpq
  apply Polynomial.eq_of_infinite_eval_eq p q
  have hinj : Function.Injective (fun n : ℕ => (n + 1 : K)) := by
    intro a b h
    have h' : (a : K) + 1 = (b : K) + 1 := by simpa using h
    exact Nat.cast_injective (add_right_cancel h')
  have hinfinite : Set.Infinite (Set.range fun n : ℕ => (n + 1 : K)) :=
    Set.infinite_range_of_injective hinj
  apply hinfinite.mono
  rintro x ⟨n, rfl⟩
  have h := congrArg (fun T : Module.End K K[X] => T (X ^ n)) hpq
  rw [aeval_yx_apply_Xpow, aeval_yx_apply_Xpow] at h
  exact smul_left_injective K (by simp : (X ^ n : K[X]) ≠ 0) (by simpa using h)

/-- The exact Weyl relation for two proposed adjacent-grade normal forms implies the
corresponding scalar polynomial identity. Injectivity of evaluation at `YX` is the
step that turns operator equality into polynomial equality. -/
theorem yx_normal_forms_commutator_eq_scalar [CharZero K] (f g : K[X])
    (h : ((aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K) -
      (aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K)) = 1) :
    X * f * g.comp (X + C (1 : K)) -
      (X - C (1 : K)) * f.comp (X - C (1 : K)) * g = -1 := by
  let P : Module.End K K[X] := aeval (yOp K * xOp K) f * yOp K
  let Q : Module.End K K[X] := aeval (yOp K * xOp K) g * xOp K
  have hQP : Q * P - P * Q = 1 := by simpa [P, Q] using h
  have hPQ : P * Q - Q * P = -1 := by
    calc
      P * Q - Q * P = -(Q * P - P * Q) := by abel
      _ = -1 := by rw [hQP]
  have hEval : aeval (yOp K * xOp K)
      (X * f * g.comp (X + C (1 : K)) -
        (X - C (1 : K)) * f.comp (X - C (1 : K)) * g) =
      aeval (yOp K * xOp K) (-1 : K[X]) := by
    rw [← yx_normal_form_commutator]
    simpa [P, Q] using hPQ
  exact aeval_yx_injective hEval

/-- For the proposed adjacent-grade normal forms, the exact relation `Q * P - P * Q = 1`
forces the coefficient polynomial of each operator to be constant. This is the local
case `(a.2)` algebra calculation; matching the source hypotheses to these normal forms is
tracked separately. -/
theorem yx_normal_forms_exact_relation_forces_factors_constant [CharZero K]
    (f g : K[X])
    (h : ((aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K) -
      (aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K)) = 1) :
    f.natDegree = 0 ∧ g.natDegree = 0 := by
  have hf : f ≠ 0 := by
    intro hf
    subst f
    simp at h
  have hg : g ≠ 0 := by
    intro hg
    subst g
    simp at h
  have hscalar := yx_normal_forms_commutator_eq_scalar f g h
  let A : K[X] := X * f * g.comp (X + C (1 : K))
  let B : K[X] := (X - C (1 : K)) * f.comp (X - C (1 : K)) * g
  have hscalar' : A - B = -1 := by simpa [A, B] using hscalar
  have hBcomp : B.comp (X + C (1 : K)) = A := by
    simp [A, B, Polynomial.comp_assoc]
  have hshift : A.comp (X + C (1 : K)) - A = -1 := by
    have hh := congrArg (fun H : K[X] => H.comp (X + C (1 : K))) hscalar'
    rw [Polynomial.sub_comp, hBcomp] at hh
    simpa using hh
  have hdiff : (X * (-f) * g.comp (X + C (1 : K))).comp
      (X + C (1 : K)) - X * (-f) * g.comp (X + C (1 : K)) = 1 := by
    have hneg : X * (-f) * g.comp (X + C (1 : K)) = -A := by
      dsimp [A]
      ring
    rw [hneg, Polynomial.neg_comp]
    calc
      -(A.comp (X + C (1 : K))) - -A =
          -(A.comp (X + C (1 : K)) - A) := by ring
      _ = 1 := by rw [hshift]; simp
  have hfac := Dixmier.shiftProduct_eq_one_forces_constant_factors
    (-f) g (neg_ne_zero.mpr hf) hg hdiff
  exact ⟨by simpa using hfac.1, hfac.2⟩

end PolynomialEvaluation

end Dixmier.Weyl
