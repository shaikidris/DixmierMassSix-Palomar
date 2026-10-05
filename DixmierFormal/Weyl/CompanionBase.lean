/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonEndpoints
public import Mathlib.Algebra.MvPolynomial.CommRing

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The base monomial of a homogeneous Poisson companion

The exact equation `{R,F}=R` forces the lowest first-coordinate exponent
of `F` to be at most one. On a strict negative-slope face of companion
weight `ρ-s`, the only exponent with first coordinate at most one is `(1,1)`.
-/

namespace Dixmier.Weyl

open MvPolynomial

private theorem pderiv_x_support_lower (p : MvPolynomial (Fin 2) ℂ)
    (a : ℕ) (hp : ∀ d ∈ p.support, a ≤ d 0)
    (i : Fin 2) (d : Fin 2 →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
    a ≤ d 0 + 1 := by
  have hc : MvPolynomial.coeff (d + Finsupp.single i 1) p ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hb := hp (d + Finsupp.single i 1) (MvPolynomial.mem_support_iff.mpr hc)
  fin_cases i <;> simp at hb ⊢ <;> omega

private theorem pderiv_y_support_lower (p : MvPolynomial (Fin 2) ℂ)
    (a : ℕ) (hp : ∀ d ∈ p.support, a ≤ d 0)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (pderiv 1 p).support) :
    a ≤ d 0 := by
  have hc : MvPolynomial.coeff (d + Finsupp.single 1 1) p ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hb := hp (d + Finsupp.single 1 1) (MvPolynomial.mem_support_iff.mpr hc)
  simpa using hb

/-- First-coordinate support order of a Poisson bracket: one derivative
can reduce the sum of the two lower bounds by at most one. -/
theorem poisson_support_x_lower (R F : MvPolynomial (Fin 2) ℂ)
    (a b : ℕ)
    (hR : ∀ d ∈ R.support, a ≤ d 0)
    (hF : ∀ d ∈ F.support, b ≤ d 0)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (poisson R F).support) :
    a + b ≤ e 0 + 1 := by
  unfold poisson at he
  have he' := MvPolynomial.support_sub (Fin 2) (pderiv 1 R * pderiv 0 F)
    (pderiv 0 R * pderiv 1 F) he
  rcases Finset.mem_union.mp he' with he' | he'
  · have he'' := MvPolynomial.support_mul (pderiv 1 R) (pderiv 0 F) he'
    obtain ⟨d, hd, f, hf, hsum⟩ := Finset.mem_add.mp he''
    have hdBound := pderiv_y_support_lower R a hR d hd
    have hfBound := pderiv_x_support_lower F b hF 0 f hf
    rw [← hsum, Finsupp.add_apply]
    omega
  · have he'' := MvPolynomial.support_mul (pderiv 0 R) (pderiv 1 F) he'
    obtain ⟨d, hd, f, hf, hsum⟩ := Finset.mem_add.mp he''
    have hdBound := pderiv_x_support_lower R a hR 0 d hd
    have hfBound := pderiv_y_support_lower F b hF f hf
    rw [← hsum, Finsupp.add_apply]
    omega

/-- A nonzero polynomial cannot satisfy `{R,F}=R` if every monomial of
`F` has first-coordinate exponent at least two. -/
theorem poisson_companion_has_small_x (R F : MvPolynomial (Fin 2) ℂ)
    (hRne : R ≠ 0) (hPoisson : poisson R F = R) :
    ∃ d ∈ F.support, d 0 ≤ 1 := by
  obtain ⟨e, he, hmin⟩ := R.support.exists_min_image
    (fun d : Fin 2 →₀ ℕ => d 0) (MvPolynomial.support_nonempty.mpr hRne)
  by_contra h
  have hF : ∀ d ∈ F.support, 2 ≤ d 0 := by
    intro d hd
    have hnot : ¬ d 0 ≤ 1 := by
      intro hle
      exact h ⟨d, hd, hle⟩
    omega
  have he' : e ∈ (poisson R F).support := by simpa [hPoisson] using he
  have hbound := poisson_support_x_lower R F (e 0) 2 hmin hF e he'
  omega

/-- On a strict negative-slope face of companion weight `ρ-s`, the exact
Poisson equation forces the coefficient of `xy` to be nonzero. -/
theorem homogeneous_companion_base_mem
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ)
    (hs : 0 < s) (hsρ : s < ρ) (hRne : R ≠ 0)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hPoisson : poisson R F = R) :
    expo 1 1 ∈ F.support := by
  obtain ⟨d, hd, hsmall⟩ := poisson_companion_has_small_x R F hRne hPoisson
  have hweight := hFhom (MvPolynomial.mem_support_iff.mp hd)
  simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hweight
  have hd0 : d 0 = 1 := by
    have hnonzero : d 0 ≠ 0 := by
      intro hz
      rw [hz] at hweight
      simp at hweight
      nlinarith
    omega
  have hd1 : d 1 = 1 := by
    rw [hd0] at hweight
    have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hmul : (s : ℤ) * (d 1 : ℤ) = (s : ℤ) * 1 := by
      linear_combination -hweight
    exact_mod_cast (mul_left_cancel₀ hsZ hmul)
  have heq : d = expo 1 1 := by
    ext i
    fin_cases i <;> simp [expo, hd0, hd1]
  simpa [← heq] using hd

end Dixmier.Weyl
