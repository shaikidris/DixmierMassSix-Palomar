/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalSupport
public import DixmierFormal.Weyl.PurePowerExclusion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal crossing exclusion at mass six

The source-supplied companion and strict-crossing support yield a quadratic
square. An exact scalar normalization puts its face into the previously
proved prime pure-power exclusion. The result is conditional on `GGVInputs`;
no restriction is placed on the mate.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem horizontal_quadratic_normalize (c β : ℂ) (hβ : β ≠ 0) :
    Polynomial.C c * (Polynomial.X - Polynomial.C β) ^ 2 =
      Polynomial.C (c * β ^ 2) *
        (1 + Polynomial.C (-β⁻¹) * Polynomial.X) ^ 2 := by
  have hβi : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  have hneg : (-β) * (-β⁻¹) = 1 := by simpa using hβi
  have hlin : Polynomial.X - Polynomial.C β =
      Polynomial.C (-β) *
        (1 + Polynomial.C (-β⁻¹) * Polynomial.X) := by
    symm
    calc
      Polynomial.C (-β) *
          (1 + Polynomial.C (-β⁻¹) * Polynomial.X) =
          Polynomial.C (-β) + Polynomial.C 1 * Polynomial.X := by
            rw [mul_add, mul_one, ← mul_assoc, ← map_mul, hneg]
      _ = Polynomial.X - Polynomial.C β := by simp; ring
  rw [hlin]
  have hs : Polynomial.C c * Polynomial.C (-β) ^ 2 =
      Polynomial.C (c * β ^ 2) := by
    rw [← map_pow, ← map_mul]
    congr 1
    ring
  rw [mul_pow, ← mul_assoc, hs]

theorem horizontal_face_normalize (μ c β : ℂ) (hβ : β ≠ 0) :
    MvPolynomial.C μ *
      (MvPolynomial.X (0 : Fin 2) *
        (Polynomial.C c * (Polynomial.X - Polynomial.C β) ^ 2).eval₂
          MvPolynomial.C (MvPolynomial.X (1 : Fin 2))) ^ 2 =
    MvPolynomial.C (μ * (c * β ^ 2) ^ 2) *
      MvPolynomial.X 0 ^ 2 *
        (1 + MvPolynomial.C (-β⁻¹) * MvPolynomial.X 1) ^ 4 := by
  rw [horizontal_quadratic_normalize c β hβ]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  simp only [map_pow, map_mul]
  ring

/-- The manuscript's complete horizontal branch, relative to the six explicit
published GGV inputs. The mate is unrestricted. -/
theorem horizontalCrossingExclusion_of_GGV
    (H : GGVInputs) : Statement.HorizontalCrossingExclusion := by
  intro P Q hpair hmass hcross
  obtain ⟨μ, c, β, hμ, hc, hβ, hface⟩ :=
    horizontal_counterexample_mass_six_scalar_shape H P Q hpair hcross hmass
  let α : ℂ := -β⁻¹
  let ν : ℂ := μ * (c * β ^ 2) ^ 2
  have hα : α ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hβ)
  have hν : ν ≠ 0 := mul_ne_zero hμ (pow_ne_zero _ (mul_ne_zero hc (pow_ne_zero _ hβ)))
  have hface' : leadingForm 1 0 P.1 = MvPolynomial.C ν *
      MvPolynomial.X 0 ^ 2 *
        (1 + MvPolynomial.C α * MvPolynomial.X 1) ^ 4 := by
    rw [hface, horizontal_face_normalize μ c β hβ]
  have hforbid := (purePowerFaceExclusion_of_GGV H) 2 0 1 2 α ν
    (by omega) (by norm_num) Nat.prime_two hα hν P Q hpair
  apply hforbid
  simpa using hface'

end Dixmier.Weyl
