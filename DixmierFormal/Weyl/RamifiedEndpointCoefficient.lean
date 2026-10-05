/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedContractionWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Extremal Laurent coefficient of a first contraction

The highest Laurent exponent in a product comes from the two highest
input exponents alone. This is the coefficient-level no-cancellation
step needed for ramified Newton endpoints.
-/

namespace Dixmier.Weyl

theorem LaurentUpper_mul_coeff_at_sum
    (f g : LaurentPolynomial ℂ) (i u : ℤ)
    (hf : LaurentUpper f i) (hg : LaurentUpper g u)
    (hfi : i ∈ f.coeff.support) :
    (f*g).coeff (i+u) = f.coeff i * g.coeff u := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ t ∈ f.coeff.support,
    f.coeff t * g.coeff (-t+(i+u))) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro t ht hti
    have hlt : t < i := lt_of_le_of_ne (hf t ht) hti
    have hnot : -t+(i+u) ∉ g.coeff.support := by
      intro hmem
      have hle := hg _ hmem
      omega
    have hz := Finsupp.notMem_support_iff.mp hnot
    simp [hz]
  · intro hnot
    exact False.elim (hnot hfi)

/-- The extremal first-contraction coefficient depends only on the
extremal Laurent coefficients of its two factors. -/
theorem ramified_first_contraction_extremal_coeff
    (l : ℕ) (f g : LaurentPolynomial ℂ) (i u : ℤ) (j k : ℕ)
    (hf : LaurentUpper f i) (hg : LaurentUpper g u)
    (hfi : i ∈ f.coeff.support) (hgu : u ∈ g.coeff.support) :
    (f * ((j : ℂ) • ramifiedDerivative l g) -
      g * ((k : ℂ) • ramifiedDerivative l f)).coeff
        (i+u-(l : ℤ)) =
      (((j : ℂ) * (u : ℂ) - (k : ℂ) * (i : ℂ)) /
        (l : ℂ)) * f.coeff i * g.coeff u := by
  have hDg : LaurentUpper (ramifiedDerivative l g) (u-(l : ℤ)) :=
    LaurentUpper_derivative l g u hg
  have hDf : LaurentUpper (ramifiedDerivative l f) (i-(l : ℤ)) :=
    LaurentUpper_derivative l f i hf
  have hsmul_g : LaurentUpper ((j : ℂ) • ramifiedDerivative l g)
      (u-(l : ℤ)) := by
    intro v hv
    change v ∈ ((j : ℂ) • (ramifiedDerivative l g).coeff).support at hv
    exact hDg v (Finsupp.support_smul hv)
  have hsmul_f : LaurentUpper ((k : ℂ) • ramifiedDerivative l f)
      (i-(l : ℤ)) := by
    intro v hv
    change v ∈ ((k : ℂ) • (ramifiedDerivative l f).coeff).support at hv
    exact hDf v (Finsupp.support_smul hv)
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  have h₁ : i+u-(l : ℤ) = i+(u-(l : ℤ)) := by omega
  rw [h₁, LaurentUpper_mul_coeff_at_sum f _ i _ hf hsmul_g hfi]
  have h₂ : i+(u-(l : ℤ)) = u+(i-(l : ℤ)) := by omega
  rw [h₂, LaurentUpper_mul_coeff_at_sum g _ u _ hg hsmul_f hgu]
  simp only [AddMonoidAlgebra.coeff_smul_apply,
    ramifiedDerivative_coeff]
  ring

theorem ramified_first_contraction_extremal_coeff_ne_zero
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (i u : ℤ) (j k : ℕ)
    (hf : LaurentUpper f i) (hg : LaurentUpper g u)
    (hfi : i ∈ f.coeff.support) (hgu : u ∈ g.coeff.support)
    (hdet : (j : ℂ) * (u : ℂ) - (k : ℂ) * (i : ℂ) ≠ 0) :
    (f * ((j : ℂ) • ramifiedDerivative l g) -
      g * ((k : ℂ) • ramifiedDerivative l f)).coeff
        (i+u-(l : ℤ)) ≠ 0 := by
  rw [ramified_first_contraction_extremal_coeff l f g i u j k
    hf hg hfi hgu]
  have hlne : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero hdet hlne)
      (Finsupp.mem_support_iff.mp hfi))
    (Finsupp.mem_support_iff.mp hgu)

end Dixmier.Weyl
