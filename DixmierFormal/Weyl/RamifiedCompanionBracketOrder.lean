/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionDiagonalStart
public import DixmierFormal.Weyl.RamifiedFirstSlopeSymmetry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# GGV's leading-bracket order

G13 Theorem 4.1 states `[P,F]_{ρ,σ} = ℓ(P)`. The first-face
coefficient and diagonal-start lemmas use `[R,P]`; the witness there
is `R = -F`. This file records the sign conversion without assuming
the stronger exact equation `[P,F] = P`.
-/

namespace Dixmier.Weyl

theorem ramifiedWeightDeg_neg (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (T : ramifiedOperatorAlgebra l) :
    ramifiedWeightDeg l hl ρ σ (-T) =
      ramifiedWeightDeg l hl ρ σ T := by
  simp only [ramifiedWeightDeg, ramifiedPBWSupport_neg]

/-- The canonical top-face equality and its attained weight imply the
coefficient relation at every point of the source's leading line,
including derivative orders absent from either support. -/
theorem ramified_source_leading_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P F : ramifiedOperatorAlgebra l)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P) :
    ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (P * F - F * P)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v := by
  intro j v hv
  calc
    ((ramifiedPBWCoeffs l hl (P * F - F * P)) j).coeff v =
        (ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P)).coeff j :=
      ramified_top_face_coeff_of_weight l hl ρ σ hρ _ j v
        (by rw [hdegree]; exact hv)
    _ = (ramifiedTopFacePolynomial l hl ρ σ P).coeff j := by rw [hface]
    _ = ((ramifiedPBWCoeffs l hl P) j).coeff v :=
      (ramified_top_face_coeff_of_weight l hl ρ σ hρ P j v hv).symm

/-- Transfer the source-order leading bracket to the order used by the
first-face polynomial identity. -/
theorem ramified_no_diagonal_start_of_source_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (P * F - F * P)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (m : ℕ) (hm : 0 < m)
    (hpoint : ((l : ℤ) * (m : ℤ), m) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ ((l : ℤ) * (m : ℤ), m) =
      ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      m ≤ j) : False := by
  have hswap : (-F) * P - P * (-F) = P * F - F * P := by
    apply Subtype.ext
    ext f
    simp
    abel
  have hFneg : -F ≠ 0 := by
    intro hz
    apply hFne
    apply Subtype.ext
    have hval := congrArg Subtype.val hz
    change -(F : Module.End ℂ (LaurentPolynomial ℂ)) = 0 at hval
    exact neg_eq_zero.mp hval
  apply ramified_no_diagonal_start_of_bracket_coeffs
    l hl ρ σ hρ hsum P (-F) hPne hFneg
  · intro j v hv
    rw [hswap]
    exact hbrcoeff j v hv
  · simpa only [ramifiedWeightDeg_neg] using hFweight
  · exact hm
  · exact hpoint
  · exact htop
  · exact hmin

/-- Source-order leading-bracket equality in the canonical finite PBW
model excludes a diagonal first point, without an exact fixed point. -/
theorem ramified_no_diagonal_start_of_source_leading_bracket
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (m : ℕ) (hm : 0 < m)
    (hpoint : ((l : ℤ) * (m : ℤ), m) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ ((l : ℤ) * (m : ℤ), m) =
      ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      m ≤ j) : False := by
  exact ramified_no_diagonal_start_of_source_bracket_coeffs
    l hl ρ σ hρ hsum P F hPne hFne
      (ramified_source_leading_bracket_coeffs l hl ρ σ hρ P F hdegree hface)
      hFweight m hm hpoint htop hmin

/-- G13 Theorem 4.1's bracket order and leading-face conclusion, when
available for an exact ramified pair, imply its non-diagonal-start
assertion. No restriction is placed on the mate's differential order. -/
theorem ramified_exact_pair_no_diagonal_start_of_source_leading_bracket
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q F : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hPweight : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ)) :
    ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = ramifiedWeightDeg l hl ρ σ P →
      (∀ q ∈ ramifiedPBWSupport l hl P,
        ramifiedWeight l ρ σ q = ramifiedWeightDeg l hl ρ σ P →
        p.2 ≤ q.2) →
      p.1 - (l : ℤ) * (p.2 : ℤ) ≠ 0 := by
  intro p hp htop hmin hdiag
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz] at hcomm
    norm_num at hcomm
  have hi : p.1 = (l : ℤ) * (p.2 : ℤ) := sub_eq_zero.mp hdiag
  have hm : 0 < p.2 := by
    by_contra h
    have hzero : p.2 = 0 := by omega
    have hi0 : p.1 = 0 := by simpa [hzero] using hi
    simp [ramifiedWeight, hi0, hzero] at htop
    omega
  have hpoint : ((l : ℤ) * (p.2 : ℤ), p.2) ∈
      ramifiedPBWSupport l hl P := by
    simpa only [← hi] using hp
  have htop' : ramifiedWeight l ρ σ ((l : ℤ) * (p.2 : ℤ), p.2) =
      ramifiedWeightDeg l hl ρ σ P := by
    simpa only [← hi] using htop
  have hmin' : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      p.2 ≤ j := by
    intro j hj
    obtain ⟨hjPBW,hjtop⟩ :=
      (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hj
    let q : ℤ × ℕ := (ramifiedPBWTopLaurent l hl P j,j)
    have hq : q ∈ ramifiedPBWSupport l hl P :=
      ramifiedPBWTopLaurent_support l hl P j hjPBW
    exact hmin q hq hjtop
  exact ramified_no_diagonal_start_of_source_leading_bracket
    l hl ρ σ hρ hsum P F hPne hFne hdegree hface hFweight
      p.2 hm hpoint htop' hmin'

end Dixmier.Weyl
