/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.LeadingMate
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Signed weighted Euler identity

Mathlib's Euler identity uses natural weights. Crossing faces in the Dixmier
argument have signed weights `(ρ, -s)`, so we prove the corresponding identity
over `ℂ` directly from homogeneous monomials.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem signedWeightedEuler (F : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hF : F.IsWeightedHomogeneous (wt ρ σ) m) :
    (ρ : ℂ) • (X 0 * pderiv 0 F) + (σ : ℂ) • (X 1 * pderiv 1 F) =
      (m : ℂ) • F := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, mul_add, smul_add]
      calc
        _ = ((ρ : ℂ) • (X 0 * pderiv 0 p) + (σ : ℂ) • (X 1 * pderiv 1 p)) +
            ((ρ : ℂ) • (X 0 * pderiv 0 q) + (σ : ℂ) • (X 1 * pderiv 1 q)) := by
              abel
        _ = (m : ℂ) • p + (m : ℂ) • q := by rw [ihp, ihq]
  | monomial d r hd =>
      simp only [X_mul_pderiv_monomial]
      have hweight : (ρ : ℤ) * (d 0 : ℤ) + σ * (d 1 : ℤ) = m := by
        rw [Finsupp.weight_eq_sum] at hd
        simpa [Fin.sum_univ_two, wt, nsmul_eq_mul, mul_comm] using hd
      have hcast : (ρ : ℂ) * (d 0 : ℂ) + (σ : ℂ) * (d 1 : ℂ) = (m : ℂ) := by
        exact_mod_cast hweight
      calc
        _ = ((ρ : ℂ) * (d 0 : ℂ) + (σ : ℂ) * (d 1 : ℂ)) •
            (monomial d r : MvPolynomial (Fin 2) ℂ) := by
              simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
        _ = (m : ℂ) • (monomial d r : MvPolynomial (Fin 2) ℂ) := by rw [hcast]

end Dixmier.Weyl
