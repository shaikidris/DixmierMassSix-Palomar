/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.WeightedFaceRigidity
public import DixmierFormal.Weyl.PoissonSubstitution

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact Poisson calculation for opposite crossing bases

For weighted faces based at the two generators, `y A(x^d y^ell)` and
`x B(x^d y^ell)`, the exact bivariate bracket is the substitution of a
univariate weighted Euler expression. Together with the coefficient theorem
in `Scalar.WeightedFaceRigidity`, this gives a short obstruction to a
bracket-one pair with a nonmonomial first face.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial
set_option maxHeartbeats 1000000

/-- Exact Poisson bracket formula for faces based at `y` and `x`. -/
theorem poisson_opposite_crossing_bases_formula (A B : ℂ[X]) (d ell : ℕ) :
    let W : MvPolynomial (Fin 2) ℂ := X 0 ^ d * X 1 ^ ell
    poisson (X 1 * A.eval₂ MvPolynomial.C W)
      (X 0 * B.eval₂ MvPolynomial.C W) =
      (A * B + Polynomial.C (d : ℂ) * A * euler B +
        Polynomial.C (ell : ℂ) * euler A * B).eval₂
        MvPolynomial.C W := by
  let W : MvPolynomial (Fin 2) ℂ := X 0 ^ d * X 1 ^ ell
  let U : MvPolynomial (Fin 2) ℂ := A.eval₂ MvPolynomial.C W
  let U' : MvPolynomial (Fin 2) ℂ := A.derivative.eval₂ MvPolynomial.C W
  let V : MvPolynomial (Fin 2) ℂ := B.eval₂ MvPolynomial.C W
  let V' : MvPolynomial (Fin 2) ℂ := B.derivative.eval₂ MvPolynomial.C W
  have hRx : X 0 * pderiv 0 (X 1 * U) =
      X 1 * (MvPolynomial.C (d : ℂ) * W * U') := by
    simpa [W, U, U', pow_zero, pow_one] using euler_crossing_x A 0 1 d ell
  have hRy : X 1 * pderiv 1 (X 1 * U) =
      X 1 * (U + MvPolynomial.C (ell : ℂ) * W * U') := by
    simpa [W, U, U', pow_zero, pow_one] using euler_crossing_y A 0 1 d ell
  have hFx : X 0 * pderiv 0 (X 0 * V) =
      X 0 * (V + MvPolynomial.C (d : ℂ) * W * V') := by
    simpa [W, V, V', pow_zero, pow_one] using euler_crossing_x B 1 0 d ell
  have hFy : X 1 * pderiv 1 (X 0 * V) =
      X 0 * (MvPolynomial.C (ell : ℂ) * W * V') := by
    simpa [W, V, V', pow_zero, pow_one] using euler_crossing_y B 1 0 d ell
  have hmul : (X 0 * X 1) * poisson (X 1 * U) (X 0 * V) =
      (X 0 * X 1) *
        (U * V + MvPolynomial.C (d : ℂ) * W * U * V' +
          MvPolynomial.C (ell : ℂ) * W * U' * V) := by
    rw [xy_mul_poisson, hRy, hFx, hRx, hFy]
    ring
  have hEval :
      (A * B + Polynomial.C (d : ℂ) * A * euler B +
          Polynomial.C (ell : ℂ) * euler A * B).eval₂
        MvPolynomial.C W =
      U * V + MvPolynomial.C (d : ℂ) * W * U * V' +
        MvPolynomial.C (ell : ℂ) * W * U' * V := by
    simp only [euler, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    dsimp [U, U', V, V']
    ring_nf
  have hxy : (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  apply mul_left_cancel₀ hxy
  calc
    (X 0 * X 1) * poisson (X 1 * A.eval₂ MvPolynomial.C W)
        (X 0 * B.eval₂ MvPolynomial.C W) =
        (X 0 * X 1) *
          (A * B + Polynomial.C (d : ℂ) * A * euler B +
            Polynomial.C (ell : ℂ) * euler A * B).eval₂
            MvPolynomial.C W := by
      calc
        _ = (X 0 * X 1) *
            (U * V + MvPolynomial.C (d : ℂ) * W * U * V' +
              MvPolynomial.C (ell : ℂ) * W * U' * V) := by simpa [U, V] using hmul
        _ = _ := by rw [hEval]

/-- If these opposite-base faces have exact bracket one, neither univariate
factor can have positive degree. -/
theorem poisson_opposite_crossing_bases_eq_one_forces_degree_zero
    (A B : ℂ[X]) (d ell : ℕ) (hell : 0 < ell)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hbr : poisson
      (X 1 * A.eval₂ MvPolynomial.C (X 0 ^ d * X 1 ^ ell))
      (X 0 * B.eval₂ MvPolynomial.C (X 0 ^ d * X 1 ^ ell)) = 1) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  let W : MvPolynomial (Fin 2) ℂ := X 0 ^ d * X 1 ^ ell
  let H : ℂ[X] := A * B + Polynomial.C (d : ℂ) * A * euler B +
    Polynomial.C (ell : ℂ) * euler A * B
  have hformula := poisson_opposite_crossing_bases_formula A B d ell
  change poisson (X 1 * A.eval₂ MvPolynomial.C W)
      (X 0 * B.eval₂ MvPolynomial.C W) = H.eval₂ MvPolynomial.C W at hformula
  have hHeval : H.eval₂ MvPolynomial.C W = 1 := by
    calc
      H.eval₂ MvPolynomial.C W =
          poisson (X 1 * A.eval₂ MvPolynomial.C W)
            (X 0 * B.eval₂ MvPolynomial.C W) := hformula.symm
      _ = 1 := by simpa [W] using hbr
  have hH : H = Polynomial.C (1 : ℂ) := by
    apply crossing_substitution_injective d ell hell
    simpa [W] using hHeval
  have hH' : H = Polynomial.C ((1 : ℕ) : ℂ) := by
    simpa only [Nat.cast_one] using hH
  exact weightedFaceEuler_eq_constant_forces_degree_zero
    (d := d) (ell := ell) (c := 1) hA hB (by simpa only [H] using hH')

end Dixmier.Weyl
