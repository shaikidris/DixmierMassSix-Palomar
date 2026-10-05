/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedTopFacePolynomial

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Derivative convolution for ramified top-face polynomials

The generic polynomial convolution and the weighted top-atom identity
are the two algebraic sides of the first-contraction Poisson formula.
-/

namespace Dixmier.Weyl

/-- The scalar derivative bracket has a finite convolution formula.
This is the commutative side of the first ramified PBW contraction. -/
theorem polynomial_derivative_bracket_coeff
    (f g : Polynomial ℂ) (α β : ℂ) (j : ℕ) :
    (Polynomial.C α * (f.derivative * g) -
      Polynomial.C β * (f * g.derivative)).coeff j =
      ∑ x ∈ Finset.antidiagonal j,
        (α * ((x.1 + 1 : ℕ) : ℂ) * f.coeff (x.1 + 1) * g.coeff x.2 -
          β * ((x.2 + 1 : ℕ) : ℂ) * f.coeff x.1 * g.coeff (x.2 + 1)) := by
  rw [Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul, Polynomial.coeff_mul]
  simp_rw [Polynomial.coeff_derivative]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  push_cast
  ring

/-- On two common top-weight faces, the Laurent exponents disappear
from the first-contraction determinant. Only the two face weights and
the derivative orders remain. -/
theorem ramified_top_pair_determinant_weight_formula
    (l : ℕ) (hl : 0 < l) (ρ σ B C A D : ℤ)
    (hρ : 0 < ρ) (n m : ℕ)
    (hP : ρ*B + (l : ℤ)*σ*(n : ℤ) = A)
    (hQ : ρ*C + (l : ℤ)*σ*(m : ℤ) = D) :
    (((n : ℂ)*(C : ℂ) - (m : ℂ)*(B : ℂ)) / (l : ℂ)) =
      (((n : ℂ)*(D : ℂ) - (m : ℂ)*(A : ℂ)) /
        ((l : ℂ)*(ρ : ℂ))) := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hPC : (ρ : ℂ)*(B : ℂ) + (l : ℂ)*(σ : ℂ)*(n : ℂ) = (A : ℂ) := by
    exact_mod_cast hP
  have hQC : (ρ : ℂ)*(C : ℂ) + (l : ℂ)*(σ : ℂ)*(m : ℂ) = (D : ℂ) := by
    exact_mod_cast hQ
  field_simp
  calc
    ((n : ℂ)*(C : ℂ) - (m : ℂ)*(B : ℂ)) * (ρ : ℂ) =
        (n : ℂ) * ((ρ : ℂ)*(C : ℂ) + (l : ℂ)*(σ : ℂ)*(m : ℂ)) -
          (m : ℂ) * ((ρ : ℂ)*(B : ℂ) + (l : ℂ)*(σ : ℂ)*(n : ℂ)) := by ring
    _ = (n : ℂ)*(D : ℂ) - (m : ℂ)*(A : ℂ) := by rw [hQC,hPC]

end Dixmier.Weyl
