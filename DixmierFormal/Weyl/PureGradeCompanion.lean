/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HomogeneousRoot

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A direct homogeneous companion for a pure nonzero grade

This is a source-faithful special case of the G13 preliminary companion
statement. It does not replace the fixed-point existence argument for a
general leading face.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The Poisson action of `xy` is minus the grade Euler operator. -/
theorem poisson_xy_eq_negative_grade_euler
    (R : MvPolynomial (Fin 2) ℂ) :
    poisson R (X 0 * X 1) =
      X 1 * pderiv 1 R - X 0 * pderiv 0 R := by
  unfold poisson
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
    MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

/-- The `xy` Poisson action is diagonal in the PBW monomial basis, with
eigenvalue equal to minus the grade. -/
theorem poisson_xy_coeff (R : MvPolynomial (Fin 2) ℂ)
    (e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e (poisson R (X 0 * X 1)) =
      ((e 1 : ℂ) - (e 0 : ℂ)) * MvPolynomial.coeff e R := by
  rw [poisson_xy_eq_negative_grade_euler]
  have hform : X 1 * pderiv 1 R - X 0 * pderiv 0 R =
      ((-1 : ℤ) : ℂ) • (X 0 * pderiv 0 R) +
        ((1 : ℤ) : ℂ) • (X 1 * pderiv 1 R) := by
    simp only [Int.cast_neg, Int.cast_one, neg_one_smul, one_smul]
    abel
  rw [hform, signedEuler_coeff_explicit]
  ring

/-- If a leading polynomial is homogeneous for grade `i-j=m≠0`, then
`-(1/m)xy` is a companion for every positive-sum Newton weight. -/
theorem pure_grade_preliminary_companion
    (R : MvPolynomial (Fin 2) ℂ) (m ρ σ : ℤ) (hm : m ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt 1 (-1)) m) :
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ + σ) ∧
      poisson R F = R := by
  let c : ℂ := -(m : ℂ)⁻¹
  let F : MvPolynomial (Fin 2) ℂ := C c * X 0 * X 1
  refine ⟨F, ?_, ?_⟩
  · have hx : (X 0 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
        (wt ρ σ) ρ := by
      simpa [wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ (wt ρ σ) 0)
    have hy : (X 1 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
        (wt ρ σ) σ := by
      simpa [wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ (wt ρ σ) 1)
    simpa [F, mul_assoc] using (hx.mul hy).C_mul c
  · have hE := signedWeightedEuler R 1 (-1) m hR
    have hPoisson : poisson R (X 0 * X 1) = -(m : ℂ) • R := by
      rw [poisson_xy_eq_negative_grade_euler]
      calc
        X 1 * pderiv 1 R - X 0 * pderiv 0 R =
            -((1 : ℂ) • (X 0 * pderiv 0 R) +
              (-1 : ℂ) • (X 1 * pderiv 1 R)) := by
                simp only [one_smul, neg_one_smul]
                abel
        _ = -(m : ℂ) • R := by
          simpa only [Int.cast_one, Int.cast_neg, neg_smul] using
            congrArg (fun z : MvPolynomial (Fin 2) ℂ => -z) hE
    have hc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hscale : c * (-(m : ℂ)) = 1 := by
      dsimp [c]
      field_simp
    change poisson R (C c * X 0 * X 1) = R
    have hlin : poisson R (C c * (X 0 * X 1)) = C c * poisson R (X 0 * X 1) := by
      unfold poisson
      simp only [MvPolynomial.pderiv_C_mul]
      ring
    rw [mul_assoc, hlin, hPoisson]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    calc
      _ = C (c * -(m : ℂ)) * R := by
        simp only [map_mul, map_neg]
        ring
      _ = R := by rw [hscale]; simp

end Dixmier.Weyl
