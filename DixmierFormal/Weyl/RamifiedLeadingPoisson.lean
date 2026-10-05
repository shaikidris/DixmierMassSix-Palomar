/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedTopFaceSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Leading Poisson coefficient of an unrestricted ramified commutator

The exact first-contraction PBW coefficient equals the derivative
bracket of the two actual canonical top-face polynomials.
-/

set_option maxHeartbeats 0

namespace Dixmier.Weyl

/-- The first exact ramified commutator face is the weighted
derivative bracket of the two actual canonical top-face polynomials. -/
theorem ramified_commutator_first_face_polynomial_bracket
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      (Polynomial.C ((ramifiedWeightDeg l hl ρ σ Q : ℂ) /
          ((l : ℂ)*(ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ P).derivative *
            ramifiedTopFacePolynomial l hl ρ σ Q) -
        Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ)*(ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ P *
            (ramifiedTopFacePolynomial l hl ρ σ Q).derivative)).coeff j := by
  classical
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  let g := ramifiedTopFacePolynomial l hl ρ σ Q
  let A := ramifiedWeightDeg l hl ρ σ P
  let D := ramifiedWeightDeg l hl ρ σ Q
  have hcomm := ramifiedPBWCoeffs_commutator_first_face_determinant
    l hl ρ σ hρ hsum P Q hPne hQne j v hv
  have hpoly := polynomial_derivative_bracket_coeff_support_pairs
    f g ((D : ℂ)/((l : ℂ)*(ρ : ℂ)))
      ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) j
  rw [hcomm]
  symm
  change (Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f.derivative*g) -
    Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f*g.derivative)).coeff j = _
  rw [hpoly]
  rw [ramifiedTopFacePolynomial_support l hl ρ σ P,
    ramifiedTopFacePolynomial_support l hl ρ σ Q]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : ρ*ramifiedPBWTopLaurent l hl P n +
      (l : ℤ)*σ*(n : ℤ) = ramifiedWeightDeg l hl ρ σ P
  · simp only [hp, if_true]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hq : ρ*ramifiedPBWTopLaurent l hl Q m +
        (l : ℤ)*σ*(m : ℤ) = ramifiedWeightDeg l hl ρ σ Q
    · simp only [hq, if_true]
      by_cases hfirst : n+m=j+1
      · simp only [hfirst, ↓reduceIte]
        have hnf : n ∈ f.support := by
          rw [ramifiedTopFacePolynomial_mem_support_iff]
          exact ⟨hn,hp⟩
        have hmg : m ∈ g.support := by
          rw [ramifiedTopFacePolynomial_mem_support_iff]
          exact ⟨hm,hq⟩
        rw [ramifiedTopFacePolynomial_coeff_of_mem_support
              l hl ρ σ P n hnf,
            ramifiedTopFacePolynomial_coeff_of_mem_support
              l hl ρ σ Q m hmg]
        rw [ramified_top_pair_determinant_weight_formula
          l hl ρ σ
          (ramifiedPBWTopLaurent l hl P n)
          (ramifiedPBWTopLaurent l hl Q m)
          A D hρ n m hp hq]
        simp only [and_true, if_true]
        ring
      · simp [hfirst]
    · simp [hq]
  · simp [hp]

/-- An exact Weyl pair has zero leading derivative-bracket coefficient
at every positive output weight on the first-contraction face. -/
theorem ramified_exact_pair_first_face_polynomial_bracket_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ))
    (hpositive : 0 < ramifiedWeight l ρ σ (v,j)) :
      (Polynomial.C ((ramifiedWeightDeg l hl ρ σ Q : ℂ) /
          ((l : ℂ)*(ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ P).derivative *
            ramifiedTopFacePolynomial l hl ρ σ Q) -
        Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ)*(ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ P *
            (ramifiedTopFacePolynomial l hl ρ σ Q).derivative)).coeff j = 0 := by
  rw [← ramified_commutator_first_face_polynomial_bracket
    l hl ρ σ hρ hsum P Q hPne hQne j v hv]
  by_contra hne
  obtain ⟨rfl,rfl⟩ :=
    (ramified_exact_pair_coeff_nonzero_iff_origin
      l hl P Q hcomm j v).mp hne
  simp [ramifiedWeight] at hpositive

end Dixmier.Weyl
