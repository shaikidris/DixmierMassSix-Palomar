/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonFixedPointDivision
public import DixmierFormal.Weyl.HomogeneousRoot

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Weight of a polynomial Poisson fixed point obtained by division

The polynomial quotient in the preceding file has the required weight
whenever its numerator and denominator are weighted homogeneous.
-/

namespace Dixmier.Weyl

open MvPolynomial

noncomputable def fixedPointEuler (ρ σ : ℤ)
    (F : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  (ρ : ℂ) • (X 0 * pderiv 0 F) + (σ : ℂ) • (X 1 * pderiv 1 F)

private theorem fixedPointEuler_mul (ρ σ : ℤ)
    (F G : MvPolynomial (Fin 2) ℂ) :
    fixedPointEuler ρ σ (F*G) =
      fixedPointEuler ρ σ F * G + F * fixedPointEuler ρ σ G := by
  simp only [fixedPointEuler, MvPolynomial.pderiv_mul,
    mul_add, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

private theorem fixedPointEuler_of_homogeneous (ρ σ m : ℤ)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F.IsWeightedHomogeneous (wt ρ σ) m) :
    fixedPointEuler ρ σ F = (m : ℂ) • F :=
  signedWeightedEuler F ρ σ m hF

private theorem homogeneous_of_fixedPointEuler (ρ σ m : ℤ)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : fixedPointEuler ρ σ F = (m : ℂ) • F) :
    F.IsWeightedHomogeneous (wt ρ σ) m := by
  intro e he
  have hc := congrArg (MvPolynomial.coeff e) hF
  simp only [fixedPointEuler, signedEuler_coeff_explicit,
    MvPolynomial.coeff_smul] at hc
  have hweight : ((Finsupp.weight (wt ρ σ) e : ℤ) : ℂ) =
      (ρ : ℂ) * (e 0 : ℂ) + (σ : ℂ) * (e 1 : ℂ) := by
    rw [Finsupp.weight_eq_sum]
    simp [Fin.sum_univ_two, wt]
    ring
  have hcoeff : MvPolynomial.coeff e F ≠ 0 := he
  have hcast : ((Finsupp.weight (wt ρ σ) e : ℤ) : ℂ) = (m : ℂ) := by
    rw [hweight]
    apply mul_right_cancel₀ hcoeff
    simpa only [smul_eq_mul] using hc
  exact_mod_cast hcast

theorem weighted_homogeneous_quotient_of_product
    (ρ σ m n r : ℤ)
    (f g h F : MvPolynomial (Fin 2) ℂ)
    (hh : h ≠ 0)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hhw : h.IsWeightedHomogeneous (wt ρ σ) r)
    (hdiv : h*F = f*g) :
    F.IsWeightedHomogeneous (wt ρ σ) (m+n-r) := by
  have hE := congrArg (fixedPointEuler ρ σ) hdiv
  rw [fixedPointEuler_mul, fixedPointEuler_mul,
    fixedPointEuler_of_homogeneous ρ σ r h hhw,
    fixedPointEuler_of_homogeneous ρ σ m f hf,
    fixedPointEuler_of_homogeneous ρ σ n g hg] at hE
  have hzero : h * (fixedPointEuler ρ σ F - ((m+n-r : ℤ) : ℂ) • F) = 0 := by
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq] at hE ⊢
    rw [show ((m + n - r : ℤ) : ℂ) = (m : ℂ) + (n : ℂ) - (r : ℂ) by push_cast; ring]
    simp only [map_add, map_sub] at hE ⊢
    ring_nf at hE ⊢
    linear_combination hE - (MvPolynomial.C (m : ℂ) +
      MvPolynomial.C (n : ℂ)) * hdiv
  have hEuler : fixedPointEuler ρ σ F = ((m+n-r : ℤ) : ℂ) • F := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hh)
  exact homogeneous_of_fixedPointEuler ρ σ (m+n-r) F hEuler

/-- Consumer-facing conditional form of the Joseph Poisson step. It
packages polynomial divisibility, the second-bracket condition, and the
homogeneous weight of the resulting fixed point. -/
theorem poisson_homogeneous_fixed_point_of_division
    (ρ σ m n : ℤ)
    (f g h F : MvPolynomial (Fin 2) ℂ)
    (hh : h ≠ 0)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hhw : h.IsWeightedHomogeneous (wt ρ σ) (m+n-(ρ+σ)))
    (hbr : poisson f g = h)
    (hcentral : poisson f h = 0)
    (hdiv : h*F = f*g) :
    poisson f F = f ∧
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) := by
  refine ⟨poisson_fixed_point_of_division f g h F hh hbr hcentral hdiv, ?_⟩
  have hw := weighted_homogeneous_quotient_of_product ρ σ m n
    (m+n-(ρ+σ)) f g h F hh hf hg hhw hdiv
  convert hw using 1; omega

end Dixmier.Weyl
