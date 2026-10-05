/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialBracketReindex

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Support of the canonical ramified top-face polynomial

The nonzero polynomial coefficients are exactly the top-weight PBW
orders, with the original Laurent leading coefficients.
-/

namespace Dixmier.Weyl

/-- The polynomial support is exactly the occupied canonical PBW
orders on the operator's actual maximum Newton face. -/
theorem ramifiedTopFacePolynomial_mem_support_iff
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) :
    j ∈ (ramifiedTopFacePolynomial l hl ρ σ T).support ↔
      j ∈ (ramifiedPBWCoeffs l hl T).support ∧
        ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T := by
  constructor
  · intro hj
    have hc := Polynomial.mem_support_iff.mp hj
    rw [ramifiedTopFacePolynomial_coeff] at hc
    split_ifs at hc with hmem htop
    · exact ⟨hmem,htop⟩
    all_goals simp at hc
  · rintro ⟨hmem,htop⟩
    apply Polynomial.mem_support_iff.mpr
    rw [ramifiedTopFacePolynomial_coeff, if_pos hmem, if_pos htop]
    exact Finsupp.mem_support_iff.mp
      (ramifiedPBWTopLaurent_mem l hl T j hmem)

theorem ramifiedTopFacePolynomial_support
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) :
    (ramifiedTopFacePolynomial l hl ρ σ T).support =
      (ramifiedPBWCoeffs l hl T).support.filter
        (fun j => ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T) := by
  classical
  ext j
  rw [ramifiedTopFacePolynomial_mem_support_iff]
  simp only [Finset.mem_filter]

theorem ramifiedTopFacePolynomial_coeff_of_mem_support
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ T).support) :
    (ramifiedTopFacePolynomial l hl ρ σ T).coeff j =
      ((ramifiedPBWCoeffs l hl T) j).coeff
        (ramifiedPBWTopLaurent l hl T j) := by
  obtain ⟨hmem,htop⟩ :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T j).mp hj
  rw [ramifiedTopFacePolynomial_coeff, if_pos hmem, if_pos htop]

/-- The derivative order of an attained maximal-order endpoint on the
actual top Newton face is the degree of its canonical polynomial. -/
theorem ramifiedTopFacePolynomial_natDegree_of_endpoint
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (N : ℕ)
    (hN : N ∈ (ramifiedPBWCoeffs l hl T).support)
    (hNtop : ρ*ramifiedPBWTopLaurent l hl T N +
      (l : ℤ)*σ*(N : ℤ) = ramifiedWeightDeg l hl ρ σ T)
    (hmax : ∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
      ρ*ramifiedPBWTopLaurent l hl T j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T →
      j ≤ N) :
    (ramifiedTopFacePolynomial l hl ρ σ T).natDegree = N := by
  have hmem : N ∈ (ramifiedTopFacePolynomial l hl ρ σ T).support :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T N).mpr
      ⟨hN,hNtop⟩
  have hle : (ramifiedTopFacePolynomial l hl ρ σ T).natDegree ≤ N := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_contra hc
    have hjs : j ∈ (ramifiedTopFacePolynomial l hl ρ σ T).support :=
      Polynomial.mem_support_iff.mpr hc
    obtain ⟨hcoeff,hw⟩ :=
      (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T j).mp hjs
    exact (not_le_of_gt hj) (hmax j hcoeff hw)
  exact Polynomial.eq_natDegree_of_le_mem_support hle hmem

end Dixmier.Weyl
