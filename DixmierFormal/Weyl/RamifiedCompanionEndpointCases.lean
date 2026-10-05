/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionRootBudget
public import DixmierFormal.Weyl.RamifiedFirstSlopeSymmetry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The two source companion endpoint cases

G13 Theorem 4.1(2) separates a parallel ending endpoint from the
exceptional `(1,1)` endpoint. The numerical work of the cut is now
complete under either source-facing case. Constructing the companion
and proving that disjunction for each exact pair remain separate.
-/

namespace Dixmier.Weyl

theorem laurentTopExponent_neg (f : LaurentPolynomial ℂ) :
    laurentTopExponent (-f) = laurentTopExponent f := by
  simp [laurentTopExponent]

/-- Negating a ramified operator changes coefficients but preserves the
canonical upper Laurent exponent at every derivative order. -/
theorem ramifiedPBWTopLaurent_neg (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) :
    ramifiedPBWTopLaurent l hl (-T) j =
      ramifiedPBWTopLaurent l hl T j := by
  simp [ramifiedPBWTopLaurent, ramifiedPBWCoeffs_neg,
    laurentTopExponent_neg]

/-- An actual ending PBW endpoint `(1,1)` has derivative order one,
so its canonical top-face polynomial is linear. Ramified first
coordinates are multiplied by `l`. -/
theorem ramifiedTopFacePolynomial_linear_of_diagonal_ending_endpoint
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l)
    (hweight : ramifiedWeightDeg l hl ρ σ T =
      (l : ℤ) * (ρ + σ))
    (hone : 1 ∈ (ramifiedPBWCoeffs l hl T).support)
    (hLaurent : ramifiedPBWTopLaurent l hl T 1 = (l : ℤ))
    (hmax : ∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
      ρ*ramifiedPBWTopLaurent l hl T j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T →
      j ≤ 1) :
    (ramifiedTopFacePolynomial l hl ρ σ T).natDegree = 1 := by
  apply ramifiedTopFacePolynomial_natDegree_of_endpoint
    l hl ρ σ T 1 hone
  · rw [hLaurent,hweight]
    push_cast
    ring
  · exact hmax

/-- The source companion uses `F`, whereas the scalar bracket convention
uses `-F`. Its ending endpoint and linear top-face degree survive this
sign conversion. -/
theorem ramifiedTopFacePolynomial_neg_linear_of_diagonal_ending_endpoint
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (F : ramifiedOperatorAlgebra l)
    (hweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hone : 1 ∈ (ramifiedPBWCoeffs l hl F).support)
    (hLaurent : ramifiedPBWTopLaurent l hl F 1 = (l : ℤ))
    (hmax : ∀ j ∈ (ramifiedPBWCoeffs l hl F).support,
      ρ*ramifiedPBWTopLaurent l hl F j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ F →
      j ≤ 1) :
    (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree = 1 := by
  have hone' : 1 ∈ (ramifiedPBWCoeffs l hl (-F)).support := by
    simpa [ramifiedPBWCoeffs_neg] using hone
  have hLaurent' : ramifiedPBWTopLaurent l hl (-F) 1 = (l : ℤ) := by
    simpa only [ramifiedPBWTopLaurent_neg] using hLaurent
  have hmax' : ∀ j ∈ (ramifiedPBWCoeffs l hl (-F)).support,
      ρ*ramifiedPBWTopLaurent l hl (-F) j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ (-F) →
      j ≤ 1 := by
    intro j hj htop
    have hjF : j ∈ (ramifiedPBWCoeffs l hl F).support := by
      simpa [ramifiedPBWCoeffs_neg] using hj
    apply hmax j hjF
    simpa only [ramifiedPBWTopLaurent_neg, ramifiedWeightDeg_neg] using htop
  apply ramifiedTopFacePolynomial_linear_of_diagonal_ending_endpoint
    l hl ρ σ (-F)
  · simpa only [ramifiedWeightDeg_neg] using hweight
  · exact hone'
  · exact hLaurent'
  · exact hmax'

/-- In the exceptional G13 endpoint case, the actual `(1,1)` endpoint
supplies the linear-face premise of the maximum-root grade argument. The
old negative ending grade remains an explicit source hypothesis. -/
theorem ramified_source_companion_diagonal_endpoint_cut_grade_negative
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l) (r : ℤ)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hweight : ramifiedWeightDeg l hl ρ σ P = ρ*r)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ P)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hone : 1 ∈ (ramifiedPBWCoeffs l hl F).support)
    (hLaurent : ramifiedPBWTopLaurent l hl F 1 = (l : ℤ))
    (hmax : ∀ j ∈ (ramifiedPBWCoeffs l hl F).support,
      ρ*ramifiedPBWTopLaurent l hl F j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ F →
      j ≤ 1)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) < 0 := by
  have hlinear := ramifiedTopFacePolynomial_neg_linear_of_diagonal_ending_endpoint
    l hl ρ σ F hFweight hone hLaurent hmax
  exact ramified_source_companion_linear_cut_grade_negative
    l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight
    hupper hdegree hface hFweight hlinear hOldEnd

/-- The parallel endpoint or the exceptional linear/full-root branch
puts the selected maximum-root cut point at nonpositive grade. -/
theorem ramified_source_companion_cut_grade_nonpositive_of_endpoint_cases
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l) (r : ℤ)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hweight : ramifiedWeightDeg l hl ρ σ P = ρ*r)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ P)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hM : 0 < (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree)
    (hcases :
      (∃ u uF : ℤ,
        ρ*u + (l : ℤ)*σ*
          ((ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)).natDegree : ℤ) = ρ*r ∧
        ρ*uF + (l : ℤ)*σ*
          ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
            (l : ℤ)*(ρ+σ) ∧
        u*((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
          uF*((ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)).natDegree : ℤ)) ∨
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree = 1 ∧
        r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
          ((ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0)) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) ≤ 0 := by
  rcases hcases with ⟨u,uF,hPend,hFend,hparallel⟩ | ⟨hlinear,hOldEnd⟩
  · exact ramified_source_companion_parallel_cut_grade_nonpositive
      l hl ρ σ hρ hdiv hsum P F r u uF hPne hFne hweight
      hupper hdegree hface hFweight hM hPend hFend hparallel
  · exact le_of_lt <|
      ramified_source_companion_linear_cut_grade_negative
        l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight
        hupper hdegree hface hFweight hlinear hOldEnd

/-- For the selected cut-grade inequality, no separate companion
endpoint disjunction is needed. The leading-bracket degree identity
handles companion degree at least two, while degree one is governed by
the old negative ending grade and the root budget. -/
theorem ramified_source_companion_cut_grade_nonpositive_of_old_end
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l) (r : ℤ)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hweight : ramifiedWeightDeg l hl ρ σ P = ρ*r)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ P)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hPdegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) ≤ 0 := by
  have hM := ramified_source_companion_top_face_degree_pos
    l hl ρ σ hρ hsum P F hPne hFne hdegree hface hFweight hPdegree
  by_cases hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree = 1
  · exact le_of_lt <|
      ramified_source_companion_linear_cut_grade_negative
        l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight
        hupper hdegree hface hFweight hlinear hOldEnd
  · exact ramified_source_companion_cut_grade_nonpositive
      l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight
      hupper hdegree hface hFweight hPdegree (by omega)

end Dixmier.Weyl
