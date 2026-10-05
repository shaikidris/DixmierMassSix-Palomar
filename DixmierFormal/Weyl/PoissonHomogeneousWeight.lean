/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonFixedPointWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Signed Newton weight of a Poisson bracket

This supplies the automatic weight of the first Joseph bracket. It uses
the exact coefficient formula for partial derivatives, including signed
weights, so no positivity restriction is needed.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem pderiv_weighted_homogeneous_signed
    (ρ σ m : ℤ) (f : MvPolynomial (Fin 2) ℂ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (i : Fin 2) :
    (pderiv i f).IsWeightedHomogeneous (wt ρ σ) (m - wt ρ σ i) := by
  intro d hd
  have hcoeff : MvPolynomial.coeff d (pderiv i f) ≠ 0 := hd
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have horig : MvPolynomial.coeff (d + Finsupp.single i 1) f ≠ 0 :=
    left_ne_zero_of_mul hcoeff
  have hw := hf horig
  have hsum : Finsupp.weight (wt ρ σ) (d + Finsupp.single i 1) =
      Finsupp.weight (wt ρ σ) d + wt ρ σ i := by
    rw [map_add]
    fin_cases i <;> simp [Finsupp.weight_eq_sum, Fin.sum_univ_two]
  rw [hsum] at hw
  omega

theorem poisson_weighted_homogeneous_signed
    (ρ σ m n : ℤ) (f g : MvPolynomial (Fin 2) ℂ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n) :
    (poisson f g).IsWeightedHomogeneous (wt ρ σ)
      (m+n-(ρ+σ)) := by
  have hfy := pderiv_weighted_homogeneous_signed ρ σ m f hf 1
  have hfx := pderiv_weighted_homogeneous_signed ρ σ m f hf 0
  have hgy := pderiv_weighted_homogeneous_signed ρ σ n g hg 1
  have hgx := pderiv_weighted_homogeneous_signed ρ σ n g hg 0
  have hleft := hfy.mul hgx
  have hright := hfx.mul hgy
  have hw0 : wt ρ σ (0 : Fin 2) = ρ := by simp [wt]
  have hw1 : wt ρ σ (1 : Fin 2) = σ := by simp [wt]
  rw [hw0, hw1] at hleft hright
  have hdeg1 : m - σ + (n - ρ) = m+n-(ρ+σ) := by omega
  have hdeg2 : m - ρ + (n - σ) = m+n-(ρ+σ) := by omega
  rw [hdeg1] at hleft
  rw [hdeg2] at hright
  exact hleft.sub hright

/-- The first Joseph bracket has the required weight automatically.
The remaining polynomiality premise is divisibility by that bracket. -/
theorem poisson_fixed_point_of_two_brackets_and_division
    (ρ σ m n : ℤ) (f g F : MvPolynomial (Fin 2) ℂ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hbr : poisson f g ≠ 0)
    (hsecond : poisson f (poisson f g) = 0)
    (hdiv : poisson f g * F = f*g) :
    poisson f F = f ∧
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) := by
  exact poisson_homogeneous_fixed_point_of_division
    ρ σ m n f g (poisson f g) F hbr hf hg
    (poisson_weighted_homogeneous_signed ρ σ m n f g hf hg)
    rfl hsecond hdiv

end Dixmier.Weyl
