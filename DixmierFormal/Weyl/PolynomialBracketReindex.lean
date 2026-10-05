/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedTopFaceDerivative

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite-support reindexing of the polynomial derivative bracket

The derivative coefficient is rewritten as a sum over pairs of
nonzero input coefficients whose degrees total one more than the
output degree.
-/

namespace Dixmier.Weyl

/-- Reindex the derivative bracket from `j` to the two face monomial
degrees whose sum is `j+1`. -/
theorem polynomial_derivative_bracket_coeff_antidiagonal_succ
    (f g : Polynomial ℂ) (α β : ℂ) (j : ℕ) :
    (Polynomial.C α * (f.derivative * g) -
      Polynomial.C β * (f * g.derivative)).coeff j =
      ∑ x ∈ Finset.antidiagonal (j+1),
        (α * (x.1 : ℂ) - β * (x.2 : ℂ)) *
          f.coeff x.1 * g.coeff x.2 := by
  rw [polynomial_derivative_bracket_coeff]
  have hleft :
      (∑ x ∈ Finset.antidiagonal (j+1),
          α * (x.1 : ℂ) * f.coeff x.1 * g.coeff x.2) =
        ∑ x ∈ Finset.antidiagonal j,
          α * ((x.1+1 : ℕ) : ℂ) * f.coeff (x.1+1) * g.coeff x.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp
  have hright :
      (∑ x ∈ Finset.antidiagonal (j+1),
          β * (x.2 : ℂ) * f.coeff x.1 * g.coeff x.2) =
        ∑ x ∈ Finset.antidiagonal j,
          β * ((x.2+1 : ℕ) : ℂ) * f.coeff x.1 * g.coeff (x.2+1) := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp
  calc
    (∑ x ∈ Finset.antidiagonal j,
        (α * ((x.1 + 1 : ℕ) : ℂ) * f.coeff (x.1 + 1) * g.coeff x.2 -
          β * ((x.2 + 1 : ℕ) : ℂ) * f.coeff x.1 * g.coeff (x.2 + 1))) =
      (∑ x ∈ Finset.antidiagonal (j+1),
        α * (x.1 : ℂ) * f.coeff x.1 * g.coeff x.2) -
      (∑ x ∈ Finset.antidiagonal (j+1),
        β * (x.2 : ℂ) * f.coeff x.1 * g.coeff x.2) := by
      rw [Finset.sum_sub_distrib, ← hleft, ← hright]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- The antidiagonal convolution may be restricted to the actual
finite supports of both polynomials. -/
theorem polynomial_derivative_bracket_coeff_support_pairs
    (f g : Polynomial ℂ) (α β : ℂ) (j : ℕ) :
    (Polynomial.C α * (f.derivative * g) -
      Polynomial.C β * (f * g.derivative)).coeff j =
      ∑ n ∈ f.support, ∑ m ∈ g.support,
        if n+m = j+1 then
          (α*(n : ℂ)-β*(m : ℂ))*f.coeff n*g.coeff m
        else 0 := by
  rw [polynomial_derivative_bracket_coeff_antidiagonal_succ]
  let F : ℕ × ℕ → ℂ := fun p =>
    (α*(p.1 : ℂ)-β*(p.2 : ℂ))*f.coeff p.1*g.coeff p.2
  have hsubset :
      ((f.support.product g.support).filter
        (fun p => p.1+p.2=j+1)) ⊆ Finset.antidiagonal (j+1) := by
    intro p hp
    exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
  have hzero : ∀ p ∈ Finset.antidiagonal (j+1),
      p ∉ (f.support.product g.support).filter
        (fun p => p.1+p.2=j+1) → F p = 0 := by
    intro p hp hnot
    have hsum : p.1+p.2=j+1 := Finset.mem_antidiagonal.mp hp
    have hprod : p ∉ f.support.product g.support := by
      intro hprod
      exact hnot (Finset.mem_filter.mpr ⟨hprod,hsum⟩)
    have hfail : p.1 ∉ f.support ∨ p.2 ∉ g.support := by
      by_cases hf : p.1 ∈ f.support
      · right
        intro hg
        exact hprod (Finset.mem_product.mpr ⟨hf,hg⟩)
      · exact Or.inl hf
    rcases hfail with hf | hg
    · have hz : f.coeff p.1 = 0 := by
        by_contra hne
        exact hf (Polynomial.mem_support_iff.mpr hne)
      simp [F,hz]
    · have hz : g.coeff p.2 = 0 := by
        by_contra hne
        exact hg (Polynomial.mem_support_iff.mpr hne)
      simp [F,hz]
  have hsumEq :
      (∑ p ∈ (f.support.product g.support).filter
        (fun p => p.1+p.2=j+1), F p) =
      ∑ p ∈ Finset.antidiagonal (j+1), F p :=
    Finset.sum_subset hsubset hzero
  rw [← hsumEq, Finset.sum_filter]
  rw [Finset.product_eq_sprod]
  simpa only [F] using
    (Finset.sum_product f.support g.support
      (fun p : ℕ × ℕ => if p.1+p.2=j+1 then F p else 0))

end Dixmier.Weyl
