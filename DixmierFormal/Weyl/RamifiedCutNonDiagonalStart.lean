/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutCanonicalStart
public import DixmierFormal.Weyl.RamifiedCompanionDiagonalStart
public import DixmierFormal.Weyl.RamifiedCompanionBracketOrder

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The selected cut point and the source non-diagonal-start assertion

The maximum-root shear makes its selected point the minimum-order point of
the old face. G13 Theorem 4.1(3), applied to the transformed pair in that
same old direction, says this point is not diagonal. This file formalizes
the transfer from that assertion; it does not prove the Joseph input.
-/

namespace Dixmier.Weyl

/-- A non-diagonal-start statement for the transformed operator implies
that the root-selected old-face point has nonzero diagonal grade. -/
theorem ramifiedCutAut_root_start_grade_ne_zero_of_nondiagonal
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hnondiagonal :
      ∀ p ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T),
        ramifiedWeight l ρ σ p =
          ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c T) →
        (∀ q ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T),
          ramifiedWeight l ρ σ q =
            ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c T) →
          p.2 ≤ q.2) →
        p.1 - (l : ℤ)*(p.2 : ℤ) ≠ 0) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl T r k)
    r-k*(m : ℤ) - (l : ℤ)*(m : ℤ) ≠ 0 := by
  dsimp only
  let k := ramifiedCutExponent l ρ σ
  let m := Polynomial.rootMultiplicity c
    (ramifiedFacePolynomial l hl T r k)
  let U := ramifiedCutAut l hl ρ σ c T
  obtain ⟨⟨hpoint,hpointWeight⟩,hmin⟩ :=
    ramifiedCutAut_root_start_on_old_face
      l hl ρ σ r i j hρ hdiv hpos c T hmem htop hupper
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c T hupper
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  apply hnondiagonal (r-k*(m : ℤ),m) hpoint
  · rw [hDeg]
    exact hpointWeight
  · intro q hq hqWeight
    exact hmin q.1 q.2 hq (by rw [hDeg] at hqWeight; exact hqWeight)

/-- The exact companion at the source weight supplies the non-diagonal
premise of the maximum-root cut. The only remaining existence input is
the weighted fixed-point operator for the transformed exact pair. -/
theorem ramifiedCutAut_root_start_grade_ne_zero_of_fixed_point
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hrpos : 0 < ρ * r) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ * r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ * r)
    (R : ramifiedOperatorAlgebra l)
    (hfixed : R * ramifiedCutAut l hl ρ σ c P -
      ramifiedCutAut l hl ρ σ c P * R =
        ramifiedCutAut l hl ρ σ c P)
    (hRweight : ramifiedWeightDeg l hl ρ σ R =
      (l : ℤ) * (ρ + σ)) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r k)
    r - k * (m : ℤ) - (l : ℤ) * (m : ℤ) ≠ 0 := by
  let U := ramifiedCutAut l hl ρ σ c P
  let V := ramifiedCutAut l hl ρ σ c Q
  have hUV : V * U - U * V = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  obtain ⟨⟨hpoint,hpointWeight⟩,_⟩ :=
    ramifiedCutAut_root_start_on_old_face
      l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c P hupper
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ * r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ * r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  have hUpos : 0 < ramifiedWeightDeg l hl ρ σ U := by
    rw [hDeg]
    exact hrpos
  exact ramifiedCutAut_root_start_grade_ne_zero_of_nondiagonal
    l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
    (ramified_exact_pair_no_diagonal_start_of_fixed_point
      l hl ρ σ hρ hpos U V R hUV hUpos hfixed hRweight)

/-- Source-facing form of the selected-grade obstruction. It requires
only the first-face bracket equality supplied by a homogeneous GGV
companion, not an exact operator fixed-point equation. -/
theorem ramifiedCutAut_root_start_grade_ne_zero_of_bracket_companion
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hrpos : 0 < ρ * r) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ * r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ * r)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) =
        ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c P) →
      ((ramifiedPBWCoeffs l hl
        (F * ramifiedCutAut l hl ρ σ c P -
          ramifiedCutAut l hl ρ σ c P * F)) j).coeff v =
      ((ramifiedPBWCoeffs l hl (ramifiedCutAut l hl ρ σ c P)) j).coeff v) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r k)
    r - k * (m : ℤ) - (l : ℤ) * (m : ℤ) ≠ 0 := by
  let U := ramifiedCutAut l hl ρ σ c P
  let V := ramifiedCutAut l hl ρ σ c Q
  have hUV : V * U - U * V = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  obtain ⟨⟨hpoint,hpointWeight⟩,_⟩ :=
    ramifiedCutAut_root_start_on_old_face
      l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c P hupper
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ * r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ * r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  have hUpos : 0 < ramifiedWeightDeg l hl ρ σ U := by
    rw [hDeg]
    exact hrpos
  exact ramifiedCutAut_root_start_grade_ne_zero_of_nondiagonal
    l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
    (ramified_exact_pair_no_diagonal_start_of_bracket_coeffs
      l hl ρ σ hρ hpos U V F hUV hUpos hFne hbrcoeff hFweight)

/-- The selected cut grade is nonzero from the homogeneous companion's
top-face polynomial equation, the precise scalar consequence of the
GGV leading-bracket statement after the bracket-sign convention is fixed. -/
theorem ramifiedCutAut_root_start_grade_ne_zero_of_top_face_equation
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hrpos : 0 < ρ * r) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ * r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ * r)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hscalar :
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ
              (ramifiedCutAut l hl ρ σ c P) : ℂ) /
            ((l : ℂ) * (ρ : ℂ))) *
            ((ramifiedTopFacePolynomial l hl ρ σ F).derivative *
              ramifiedTopFacePolynomial l hl ρ σ
                (ramifiedCutAut l hl ρ σ c P)) -
        Polynomial.C ((ramifiedWeightDeg l hl ρ σ F : ℂ) /
            ((l : ℂ) * (ρ : ℂ))) *
            (ramifiedTopFacePolynomial l hl ρ σ F *
              (ramifiedTopFacePolynomial l hl ρ σ
                (ramifiedCutAut l hl ρ σ c P)).derivative) =
        ramifiedTopFacePolynomial l hl ρ σ
          (ramifiedCutAut l hl ρ σ c P)) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r k)
    r - k * (m : ℤ) - (l : ℤ) * (m : ℤ) ≠ 0 := by
  let U := ramifiedCutAut l hl ρ σ c P
  let V := ramifiedCutAut l hl ρ σ c Q
  have hUV : V * U - U * V = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  obtain ⟨⟨hpoint,hpointWeight⟩,_⟩ :=
    ramifiedCutAut_root_start_on_old_face
      l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c P hupper
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ * r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ * r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  have hUpos : 0 < ramifiedWeightDeg l hl ρ σ U := by
    rw [hDeg]
    exact hrpos
  exact ramifiedCutAut_root_start_grade_ne_zero_of_nondiagonal
    l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
    (ramified_exact_pair_no_diagonal_start_of_top_face_equation
      l hl ρ σ hρ hpos U V F hUV hUpos hFne hFweight hscalar)

/-- Apply the published-order leading-bracket interface of G13
Theorem 4.1 directly to the exact pair after the maximum-root shear.
The source companion's existence is still a separate obligation. -/
theorem ramifiedCutAut_root_start_grade_ne_zero_of_source_leading_bracket
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hrpos : 0 < ρ * r) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ * r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ * r)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hdegree : ramifiedWeightDeg l hl ρ σ
        (ramifiedCutAut l hl ρ σ c P * F -
          F * ramifiedCutAut l hl ρ σ c P) =
      ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c P))
    (hface : ramifiedTopFacePolynomial l hl ρ σ
        (ramifiedCutAut l hl ρ σ c P * F -
          F * ramifiedCutAut l hl ρ σ c P) =
      ramifiedTopFacePolynomial l hl ρ σ
        (ramifiedCutAut l hl ρ σ c P)) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r k)
    r - k * (m : ℤ) - (l : ℤ) * (m : ℤ) ≠ 0 := by
  let U := ramifiedCutAut l hl ρ σ c P
  let V := ramifiedCutAut l hl ρ σ c Q
  have hUV : V * U - U * V = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  obtain ⟨⟨hpoint,hpointWeight⟩,_⟩ :=
    ramifiedCutAut_root_start_on_old_face
      l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c P hupper
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ * r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ * r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  have hUpos : 0 < ramifiedWeightDeg l hl ρ σ U := by
    rw [hDeg]
    exact hrpos
  exact ramifiedCutAut_root_start_grade_ne_zero_of_nondiagonal
    l hl ρ σ r i j hρ hdiv hpos c P hmem htop hupper
    (ramified_exact_pair_no_diagonal_start_of_source_leading_bracket
      l hl ρ σ hρ hpos U V F hUV hUpos hFne hdegree hface hFweight)

end Dixmier.Weyl
