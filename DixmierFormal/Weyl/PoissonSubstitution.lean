/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CompanionShape
public import DixmierFormal.Scalar.Defs
public import DixmierFormal.Weyl.CrossingTermCount

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Crossing-face Poisson equation and scalar companion equation

The polynomial chain rule and coordinate Euler identities give the exact
Poisson formula for `R=x^a y^b r(x^s y^ρ)` and `F=xy f(x^s y^ρ)`.
Cancellation in the polynomial domain and injectivity of the substitution
then yield the paper's scalar equation (5.2). This module assumes the displayed
forms of `R` and `F`; extracting `R` from an arbitrary crossing face remains
a separate obligation.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial
set_option maxHeartbeats 1000000

/-- Polynomial chain rule for a univariate polynomial evaluated at a bivariate
polynomial. -/
theorem pderiv_polynomial_substitution (r : ℂ[X])
    (W : MvPolynomial (Fin 2) ℂ) (i : Fin 2) :
    MvPolynomial.pderiv i (r.eval₂ MvPolynomial.C W) =
      (r.derivative.eval₂ MvPolynomial.C W) * MvPolynomial.pderiv i W := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval₂_add, map_add, hp, hq, add_mul]
  | monomial n c =>
      simp [Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
        mul_assoc, mul_comm, mul_left_comm]

theorem euler_X_pow (i : Fin 2) (n : ℕ) :
    X i * pderiv i (X i ^ n : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.C (n : ℂ) * X i ^ n := by
  rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
  by_cases hn : n = 0
  · subst n
    simp
  · have hpred : X i ^ (n - 1) * X i = (X i : MvPolynomial (Fin 2) ℂ) ^ n := by
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using
        (pow_succ (X i : MvPolynomial (Fin 2) ℂ) (n - 1)).symm
    rw [show (n : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C (n : ℂ) by simp]
    calc
      X i * (MvPolynomial.C (n : ℂ) * X i ^ (n - 1)) =
          MvPolynomial.C (n : ℂ) * (X i ^ (n - 1) * X i) := by ring
      _ = MvPolynomial.C (n : ℂ) * X i ^ n := by rw [hpred]

theorem euler_other_X_pow (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    X i * pderiv i (X j ^ n : MvPolynomial (Fin 2) ℂ) = 0 := by
  rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne hij.symm]
  simp

theorem euler_substitution_x (s ρ : ℕ) :
    X 0 * pderiv 0 (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.C (s : ℂ) * (X 0 ^ s * X 1 ^ ρ) := by
  rw [MvPolynomial.pderiv_mul]
  have hother := euler_other_X_pow 0 1 (by decide) ρ
  have hself := euler_X_pow 0 s
  calc
    X (0 : Fin 2) * (pderiv 0 (X 0 ^ s) * X 1 ^ ρ + X 0 ^ s * pderiv 0 (X 1 ^ ρ)) =
        (X (0 : Fin 2) * pderiv 0 (X 0 ^ s)) * X 1 ^ ρ +
          X 0 ^ s * (X (0 : Fin 2) * pderiv 0 (X 1 ^ ρ)) := by ring
    _ = MvPolynomial.C (s : ℂ) * (X 0 ^ s * X 1 ^ ρ) := by rw [hself, hother]; ring

theorem euler_substitution_y (s ρ : ℕ) :
    X 1 * pderiv 1 (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.C (ρ : ℂ) * (X 0 ^ s * X 1 ^ ρ) := by
  rw [MvPolynomial.pderiv_mul]
  have hother := euler_other_X_pow 1 0 (by decide) s
  have hself := euler_X_pow 1 ρ
  calc
    X (1 : Fin 2) * (pderiv 1 (X 0 ^ s) * X 1 ^ ρ + X 0 ^ s * pderiv 1 (X 1 ^ ρ)) =
        (X (1 : Fin 2) * pderiv 1 (X 0 ^ s)) * X 1 ^ ρ +
          X 0 ^ s * (X (1 : Fin 2) * pderiv 1 (X 1 ^ ρ)) := by ring
    _ = MvPolynomial.C (ρ : ℂ) * (X 0 ^ s * X 1 ^ ρ) := by rw [hself, hother]; ring

theorem euler_eval_x (r : ℂ[X]) (s ρ : ℕ) :
    X 0 * pderiv 0 (r.eval₂ MvPolynomial.C
      (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ)) =
      MvPolynomial.C (s : ℂ) * (X 0 ^ s * X 1 ^ ρ) *
        (r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) := by
  rw [pderiv_polynomial_substitution]
  have h := euler_substitution_x s ρ
  calc
    X (0 : Fin 2) *
        ((r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) *
          pderiv 0 (X 0 ^ s * X 1 ^ ρ)) =
        (X 0 * pderiv 0 (X 0 ^ s * X 1 ^ ρ)) *
          (r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) := by ring
    _ = _ := by rw [h]

theorem euler_eval_y (r : ℂ[X]) (s ρ : ℕ) :
    X 1 * pderiv 1 (r.eval₂ MvPolynomial.C
      (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ)) =
      MvPolynomial.C (ρ : ℂ) * (X 0 ^ s * X 1 ^ ρ) *
        (r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) := by
  rw [pderiv_polynomial_substitution]
  have h := euler_substitution_y s ρ
  calc
    X (1 : Fin 2) *
        ((r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) *
          pderiv 1 (X 0 ^ s * X 1 ^ ρ)) =
        (X 1 * pderiv 1 (X 0 ^ s * X 1 ^ ρ)) *
          (r.derivative.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) := by ring
    _ = _ := by rw [h]

theorem euler_monomial_x (a b : ℕ) :
    X 0 * pderiv 0 (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.C (a : ℂ) * (X 0 ^ a * X 1 ^ b) := by
  simpa only [] using euler_substitution_x a b

theorem euler_monomial_y (a b : ℕ) :
    X 1 * pderiv 1 (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.C (b : ℂ) * (X 0 ^ a * X 1 ^ b) := by
  simpa only [] using euler_substitution_y a b

theorem euler_crossing_x (r : ℂ[X]) (a b s ρ : ℕ) :
    let A : MvPolynomial (Fin 2) ℂ := X 0 ^ a * X 1 ^ b
    let W : MvPolynomial (Fin 2) ℂ := X 0 ^ s * X 1 ^ ρ
    let U := r.eval₂ MvPolynomial.C W
    let U' := r.derivative.eval₂ MvPolynomial.C W
    X 0 * pderiv 0 (A * U) = A * (MvPolynomial.C (a : ℂ) * U +
      MvPolynomial.C (s : ℂ) * W * U') := by
  dsimp
  rw [MvPolynomial.pderiv_mul]
  have hA := euler_monomial_x a b
  have hU := euler_eval_x r s ρ
  calc
    X (0 : Fin 2) *
      (pderiv 0 (X 0 ^ a * X 1 ^ b) *
          r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ) +
        (X 0 ^ a * X 1 ^ b) *
          pderiv 0 (r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))) =
      (X 0 * pderiv 0 (X 0 ^ a * X 1 ^ b)) *
          r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ) +
        (X 0 ^ a * X 1 ^ b) *
          (X 0 * pderiv 0 (r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))) := by ring
    _ = _ := by rw [hA, hU]; ring

theorem euler_crossing_y (r : ℂ[X]) (a b s ρ : ℕ) :
    let A : MvPolynomial (Fin 2) ℂ := X 0 ^ a * X 1 ^ b
    let W : MvPolynomial (Fin 2) ℂ := X 0 ^ s * X 1 ^ ρ
    let U := r.eval₂ MvPolynomial.C W
    let U' := r.derivative.eval₂ MvPolynomial.C W
    X 1 * pderiv 1 (A * U) = A * (MvPolynomial.C (b : ℂ) * U +
      MvPolynomial.C (ρ : ℂ) * W * U') := by
  dsimp
  rw [MvPolynomial.pderiv_mul]
  have hA := euler_monomial_y a b
  have hU := euler_eval_y r s ρ
  calc
    X (1 : Fin 2) *
      (pderiv 1 (X 0 ^ a * X 1 ^ b) *
          r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ) +
        (X 0 ^ a * X 1 ^ b) *
          pderiv 1 (r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))) =
      (X 1 * pderiv 1 (X 0 ^ a * X 1 ^ b)) *
          r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ) +
        (X 0 ^ a * X 1 ^ b) *
          (X 1 * pderiv 1 (r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))) := by ring
    _ = _ := by rw [hA, hU]; ring

theorem xy_mul_poisson (R F : MvPolynomial (Fin 2) ℂ) :
    (X 0 * X 1) * poisson R F =
      (X 1 * pderiv 1 R) * (X 0 * pderiv 0 F) -
        (X 0 * pderiv 0 R) * (X 1 * pderiv 1 F) := by
  unfold poisson
  ring

/-- The exact bivariate Poisson calculation, after multiplying by `xy` to avoid
negative exponents at the zero-exponent boundaries. -/
theorem crossing_poisson_formula (r f : ℂ[X]) (a b s ρ : ℕ) :
    let A : MvPolynomial (Fin 2) ℂ := X 0 ^ a * X 1 ^ b
    let W : MvPolynomial (Fin 2) ℂ := X 0 ^ s * X 1 ^ ρ
    let U := r.eval₂ MvPolynomial.C W
    let V := f.eval₂ MvPolynomial.C W
    let U' := r.derivative.eval₂ MvPolynomial.C W
    let V' := f.derivative.eval₂ MvPolynomial.C W
    (X 0 * X 1) * poisson (A * U) ((X 0 * X 1) * V) =
      A * (X 0 * X 1) *
        (((MvPolynomial.C (ρ : ℂ) - MvPolynomial.C (s : ℂ)) * W * V * U') -
          (((MvPolynomial.C (a : ℂ) - MvPolynomial.C (b : ℂ)) * V +
            (MvPolynomial.C (ρ : ℂ) * MvPolynomial.C (a : ℂ) -
              MvPolynomial.C (s : ℂ) * MvPolynomial.C (b : ℂ)) * W * V') * U)) := by
  dsimp
  rw [xy_mul_poisson]
  have hRx := euler_crossing_x r a b s ρ
  have hRy := euler_crossing_y r a b s ρ
  have hFx := euler_crossing_x f 1 1 s ρ
  have hFy := euler_crossing_y f 1 1 s ρ
  simp only [pow_one] at hFx hFy
  rw [hRx, hRy, hFx, hFy]
  norm_num only [Nat.cast_one, map_one]
  ring

/-- Substitution by `x^s y^ρ` is injective for positive `ρ`, witnessed by
specializing `x=1` and applying the injectivity of polynomial expansion. -/
theorem crossing_substitution_injective (s ρ : ℕ) (hρ : 0 < ρ) :
    Function.Injective (fun r : ℂ[X] => r.eval₂ MvPolynomial.C
      (X 0 ^ s * X 1 ^ ρ : MvPolynomial (Fin 2) ℂ)) := by
  intro r f h
  have heval := congrArg (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)) h
  rw [crossing_substitution_eval, crossing_substitution_eval] at heval
  apply Polynomial.expand_injective (R := ℂ) hρ
  simpa only [Polynomial.expand_eq_comp_X_pow] using heval

/-- The general scalar companion equation (paper equation (5.2)) follows
from the bivariate Poisson equation for the displayed crossing-face forms. -/
theorem crossing_poisson_implies_scalar
    (r f : ℂ[X]) (a b s ρ : ℕ) (hρ : 0 < ρ)
    (hbr : poisson
      ((X 0 ^ a * X 1 ^ b) *
        r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))
      ((X 0 * X 1) *
        f.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) =
      (X 0 ^ a * X 1 ^ b) *
        r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) :
    (Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r)) = 0 := by
  let A : MvPolynomial (Fin 2) ℂ := X 0 ^ a * X 1 ^ b
  let W : MvPolynomial (Fin 2) ℂ := X 0 ^ s * X 1 ^ ρ
  let U := r.eval₂ MvPolynomial.C W
  let V := f.eval₂ MvPolynomial.C W
  let U' := r.derivative.eval₂ MvPolynomial.C W
  let V' := f.derivative.eval₂ MvPolynomial.C W
  let B : MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.C (ρ : ℂ) - MvPolynomial.C (s : ℂ)) * W * V * U' -
      ((MvPolynomial.C (a : ℂ) - MvPolynomial.C (b : ℂ)) * V +
        (MvPolynomial.C (ρ : ℂ) * MvPolynomial.C (a : ℂ) -
          MvPolynomial.C (s : ℂ) * MvPolynomial.C (b : ℂ)) * W * V') * U
  have hformula := crossing_poisson_formula r f a b s ρ
  change (X 0 * X 1) * poisson (A * U) ((X 0 * X 1) * V) =
    A * (X 0 * X 1) * B at hformula
  change poisson (A * U) ((X 0 * X 1) * V) = A * U at hbr
  rw [hbr] at hformula
  have hA : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero 0))
      (pow_ne_zero _ (MvPolynomial.X_ne_zero 1))
  have hxy : (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  have hBU : B = U := by
    apply mul_left_cancel₀ (mul_ne_zero hA hxy)
    calc
      (A * (X 0 * X 1)) * B = (X 0 * X 1) * (A * U) := by simpa only [mul_assoc] using hformula.symm
      _ = (A * (X 0 * X 1)) * U := by ring
  apply (crossing_substitution_injective s ρ hρ)
  have hEval : (Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r)).eval₂
      MvPolynomial.C W = 0 := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    dsimp [B, U, V, U', V'] at hBU
    convert sub_eq_zero.mpr hBU using 1
    simp only [map_sub, map_mul]
    ring
  simpa only [Polynomial.eval₂_zero] using hEval

/-- At starting exponent `(a,b)=(1,0)`, the general equation is exactly the
frozen scalar companion equation used by Theorem 1.2. -/
theorem crossing_poisson_implies_companionEq
    (r f : ℂ[X]) (s ρ : ℕ) (hρ : 0 < ρ)
    (hbr : poisson
      ((X 0 : MvPolynomial (Fin 2) ℂ) *
        r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ))
      ((X 0 * X 1) *
        f.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) =
      X 0 * r.eval₂ MvPolynomial.C (X 0 ^ s * X 1 ^ ρ)) :
    Dixmier.CompanionEq (ρ : ℤ) (s : ℤ) r f := by
  have h := crossing_poisson_implies_scalar r f 1 0 s ρ hρ
    (by simpa using hbr)
  unfold Dixmier.CompanionEq
  convert h using 1
  norm_num

end Dixmier.Weyl
