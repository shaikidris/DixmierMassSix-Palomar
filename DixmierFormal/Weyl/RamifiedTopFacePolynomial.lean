/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstFaceExact

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical top-face polynomial of a ramified operator

The actual finite PBW maximum selects a nonzero ordinary polynomial,
without an externally chosen support box or derivative-order cutoff.
-/

namespace Dixmier.Weyl

/-- The finite polynomial in derivative order formed from the actual
canonical top Newton atoms of a ramified operator. -/
noncomputable def ramifiedTopFacePolynomial
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) : Polynomial ℂ :=
  Polynomial.ofFinsupp ⟨
    Finsupp.onFinset (ramifiedPBWCoeffs l hl T).support
      (fun j => if ρ*ramifiedPBWTopLaurent l hl T j +
                    (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T then
          ((ramifiedPBWCoeffs l hl T) j).coeff
            (ramifiedPBWTopLaurent l hl T j) else 0)
      (by
        intro j hj
        apply Finsupp.mem_support_iff.mpr
        intro hz
        simp [hz] at hj)⟩

@[simp] theorem ramifiedTopFacePolynomial_coeff
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) :
    (ramifiedTopFacePolynomial l hl ρ σ T).coeff j =
      if j ∈ (ramifiedPBWCoeffs l hl T).support then
        if ρ*ramifiedPBWTopLaurent l hl T j +
            (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T then
          ((ramifiedPBWCoeffs l hl T) j).coeff
            (ramifiedPBWTopLaurent l hl T j)
        else 0
      else 0 := by
  by_cases hj : j ∈ (ramifiedPBWCoeffs l hl T).support
  · simp [ramifiedTopFacePolynomial, Finsupp.onFinset_apply, hj]
  · have hz : (ramifiedPBWCoeffs l hl T) j = 0 := by
      by_contra hne
      exact hj (Finsupp.mem_support_iff.mpr hne)
    simp [ramifiedTopFacePolynomial, Finsupp.onFinset_apply, hj, hz]

/-- A nonzero ramified operator has a nonzero canonical top-face
polynomial in every direction with positive horizontal weight. -/
theorem ramifiedTopFacePolynomial_ne_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l) (hT : T ≠ 0) :
    ramifiedTopFacePolynomial l hl ρ σ T ≠ 0 := by
  obtain ⟨A,N,hN,_,hNtop,_,hNcoeff,hA⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ T
      (ramifiedPBWSupport_nonempty_of_ne_zero l hl T hT)
  intro hz
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff N) hz
  rw [ramifiedTopFacePolynomial_coeff, if_pos hN,
    if_pos (by simpa [hA] using hNtop)] at hc
  simp at hc
  exact (Finsupp.mem_support_iff.mp hNcoeff) hc

end Dixmier.Weyl
