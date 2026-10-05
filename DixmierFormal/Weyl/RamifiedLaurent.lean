/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Tactic.FieldSimp

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The scaled derivative on a ramified Laurent coefficient ring

For `l > 0`, write `T = X^(1/l)`. The differential operator `Y = d/dX`
acts on `T^n` by `(n/l) T^(n-l)`. This is a foundation for the
ramified Weyl algebra used in G13's shape cut. It does not formalize
the cut or its automorphisms.
-/

namespace Dixmier.Weyl

open LaurentPolynomial

/-- The scaled derivative `d/dX` on Laurent polynomials in `T=X^(1/l)`. -/
noncomputable def ramifiedDerivative (l : ℕ) :
    LaurentPolynomial ℂ →ₗ[ℂ] LaurentPolynomial ℂ :=
  ((Finsupp.lsum ℂ) (fun n : ℤ =>
    (LinearMap.mulLeft ℂ ((n : ℂ) / (l : ℂ))).smulRight
      (LaurentPolynomial.T (n - (l : ℤ))))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem ramifiedDerivative_single (l : ℕ) (n : ℤ) (c : ℂ) :
    ramifiedDerivative l (AddMonoidAlgebra.single n c) =
      ((n : ℂ) / (l : ℂ) * c) •
        (T (n - (l : ℤ)) : LaurentPolynomial ℂ) := by
  simp [ramifiedDerivative, -LaurentPolynomial.single_eq_C_mul_T]

theorem ramifiedDerivative_T (l : ℕ) (n : ℤ) :
    ramifiedDerivative l (T n) =
      ((n : ℂ) / (l : ℂ)) •
        (T (n - (l : ℤ)) : LaurentPolynomial ℂ) := by
  simpa only [LaurentPolynomial.T, mul_one] using
    ramifiedDerivative_single l n 1

/-- Leibniz on Laurent monomial pairs. -/
theorem ramifiedDerivative_T_mul_T (l : ℕ) (m n : ℤ) :
    ramifiedDerivative l ((T m : LaurentPolynomial ℂ) * T n) =
      ramifiedDerivative l (T m) * T n +
      T m * ramifiedDerivative l (T n) := by
  rw [← T_add, ramifiedDerivative_T, ramifiedDerivative_T,
    ramifiedDerivative_T, smul_mul_assoc, mul_smul_comm,
    ← T_add, ← T_add]
  have h₁ : m - (l : ℤ) + n = m + n - (l : ℤ) := by omega
  have h₂ : m + (n - (l : ℤ)) = m + n - (l : ℤ) := by omega
  rw [h₁, h₂, ← add_smul]
  have hc : (((m + n : ℤ) : ℂ) / (l : ℂ)) =
      (m : ℂ) / (l : ℂ) + (n : ℂ) / (l : ℂ) := by
    push_cast
    ring
  rw [hc]

/-- Leibniz for a Laurent monomial times any Laurent polynomial. -/
theorem ramifiedDerivative_T_mul (l : ℕ) (m : ℤ)
    (g : LaurentPolynomial ℂ) :
    ramifiedDerivative l (T m * g) =
      ramifiedDerivative l (T m) * g +
      T m * ramifiedDerivative l g := by
  induction g using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      calc
        ramifiedDerivative l (T m * (p + q)) =
            ramifiedDerivative l (T m * p) +
              ramifiedDerivative l (T m * q) := by simp only [mul_add, map_add]
        _ = (ramifiedDerivative l (T m) * p + T m * ramifiedDerivative l p) +
            (ramifiedDerivative l (T m) * q + T m * ramifiedDerivative l q) := by
              rw [hp, hq]
        _ = ramifiedDerivative l (T m) * (p + q) +
              T m * ramifiedDerivative l (p + q) := by
              simp only [mul_add, map_add]
              abel
  | C_mul_T n c =>
      rw [← LaurentPolynomial.smul_eq_C_mul]
      rw [mul_smul_comm, map_smul, map_smul, mul_smul_comm]
      simpa only [smul_add, smul_mul_assoc, mul_smul_comm] using
        congrArg (fun z : LaurentPolynomial ℂ => c • z)
          (ramifiedDerivative_T_mul_T l m n)

/-- The scaled derivative satisfies Leibniz on the full Laurent ring. -/
theorem ramifiedDerivative_mul (l : ℕ)
    (f g : LaurentPolynomial ℂ) :
    ramifiedDerivative l (f * g) =
      ramifiedDerivative l f * g + f * ramifiedDerivative l g := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      calc
        ramifiedDerivative l ((p + q) * g) =
            ramifiedDerivative l (p * g) +
              ramifiedDerivative l (q * g) := by simp only [add_mul, map_add]
        _ = (ramifiedDerivative l p * g + p * ramifiedDerivative l g) +
            (ramifiedDerivative l q * g + q * ramifiedDerivative l g) := by
              rw [hp, hq]
        _ = ramifiedDerivative l (p + q) * g +
              (p + q) * ramifiedDerivative l g := by
              simp only [add_mul, map_add]
              abel
  | C_mul_T n c =>
      rw [← LaurentPolynomial.smul_eq_C_mul]
      rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc]
      simpa only [smul_add, smul_mul_assoc] using
        congrArg (fun z : LaurentPolynomial ℂ => c • z)
          (ramifiedDerivative_T_mul l n g)

/-- On every Laurent monomial, `Y X - X Y = 1`, with `X=T^l`. -/
theorem ramifiedDerivative_X_comm (l : ℕ) (hl : 0 < l) (n : ℤ) :
    ramifiedDerivative l ((T (l : ℤ)) * (T n)) -
      (T (l : ℤ)) * ramifiedDerivative l (T n) = T n := by
  rw [← T_add, ramifiedDerivative_T, ramifiedDerivative_T]
  simp only [add_sub_cancel_left]
  rw [mul_smul_comm, ← T_add]
  have he : (l : ℤ) + (n - (l : ℤ)) = n := by omega
  rw [he]
  have hln : (l : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hc : (((l : ℤ) + n : ℤ) : ℂ) / (l : ℂ) -
      (n : ℂ) / (l : ℂ) = 1 := by
    push_cast
    field_simp [hln]
    ring
  rw [← sub_smul, hc, one_smul]

/-- The exact Weyl relation acts as the identity on every ramified
Laurent polynomial, not only on basis monomials. -/
theorem ramifiedDerivative_X_comm_all (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) :
    ramifiedDerivative l ((T (l : ℤ)) * f) -
      (T (l : ℤ)) * ramifiedDerivative l f = f := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      calc
        ramifiedDerivative l (T (l : ℤ) * (p + q)) -
            T (l : ℤ) * ramifiedDerivative l (p + q) =
            (ramifiedDerivative l (T (l : ℤ) * p) -
              T (l : ℤ) * ramifiedDerivative l p) +
            (ramifiedDerivative l (T (l : ℤ) * q) -
              T (l : ℤ) * ramifiedDerivative l q) := by
                simp only [mul_add, map_add]
                abel
        _ = p + q := by rw [hp, hq]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.smul_eq_C_mul]
      rw [mul_smul_comm, map_smul, map_smul, mul_smul_comm]
      simpa only [smul_sub] using
        congrArg (fun z : LaurentPolynomial ℂ => c • z)
          (ramifiedDerivative_X_comm l hl n)

/-- Multiplication by `X=T^l` as a linear endomorphism. -/
noncomputable def ramifiedX (l : ℕ) :
    Module.End ℂ (LaurentPolynomial ℂ) :=
  LinearMap.mulLeft ℂ (T (l : ℤ))

/-- The ramified `X` and `Y` operators obey the Weyl relation as
endomorphisms of the entire Laurent coefficient ring. -/
theorem ramifiedEnd_comm (l : ℕ) (hl : 0 < l) :
    ramifiedDerivative l * ramifiedX l -
      ramifiedX l * ramifiedDerivative l = 1 := by
  apply LinearMap.ext
  intro f
  change ramifiedDerivative l (T (l : ℤ) * f) -
    T (l : ℤ) * ramifiedDerivative l f = f
  exact ramifiedDerivative_X_comm_all l hl f

end Dixmier.Weyl
