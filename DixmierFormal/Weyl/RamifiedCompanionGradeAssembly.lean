/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionEndpointCases
public import DixmierFormal.Weyl.RamifiedCutNonDiagonalStart
public import DixmierFormal.Weyl.RamifiedShearTopFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Strict maximum-root grade from pre- and post-cut source companions

The pre-cut companion and original negative ending grade give a
nonpositive bound. The post-cut source companion excludes equality.
These may be different witnesses; no equality between them is assumed.
-/

namespace Dixmier.Weyl

theorem ramifiedCutAut_maxRoot_grade_negative_of_source_companions
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ) (hrpos : 0 < ρ*r)
    (c : ℂ) (P Q Fpre Fpost : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (hPne : P ≠ 0) (hFpreNe : Fpre ≠ 0)
    (hFpostNe : Fpost ≠ 0)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hpreDegree : ramifiedWeightDeg l hl ρ σ (P*Fpre-Fpre*P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hpreFace : ramifiedTopFacePolynomial l hl ρ σ
      (P*Fpre-Fpre*P) = ramifiedTopFacePolynomial l hl ρ σ P)
    (hpreWeight : ramifiedWeightDeg l hl ρ σ Fpre =
      (l : ℤ)*(ρ+σ))
    (hPtopDegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0)
    (hmaxRoot : Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r (ramifiedCutExponent l ρ σ)) =
        maxRootMult (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)))
    (hpostWeight : ramifiedWeightDeg l hl ρ σ Fpost =
      (l : ℤ)*(ρ+σ))
    (hpostDegree : ramifiedWeightDeg l hl ρ σ
      (ramifiedCutAut l hl ρ σ c P * Fpost -
        Fpost * ramifiedCutAut l hl ρ σ c P) =
      ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c P))
    (hpostFace : ramifiedTopFacePolynomial l hl ρ σ
      (ramifiedCutAut l hl ρ σ c P * Fpost -
        Fpost * ramifiedCutAut l hl ρ σ c P) =
      ramifiedTopFacePolynomial l hl ρ σ
        (ramifiedCutAut l hl ρ σ c P)) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (Polynomial.rootMultiplicity c
        (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) : ℤ) < 0 := by
  have hPweight : ramifiedWeightDeg l hl ρ σ P = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) P
      ⟨(i,j),hmem,htop⟩
      (fun p hp => hupper p.1 p.2 hp)
  have hnonpositive :=
    ramified_source_companion_cut_grade_nonpositive_of_old_end
      l hl ρ σ hρ hdiv hsum P Fpre r hPne hFpreNe hPweight
      (fun p hp => by rw [hPweight]; exact hupper p.1 p.2 hp)
      hpreDegree hpreFace hpreWeight hPtopDegree hOldEnd
  have hnonzero :=
    ramifiedCutAut_root_start_grade_ne_zero_of_source_leading_bracket
      l hl ρ σ r i j hρ hdiv hsum hrpos c P Q hcomm
      hmem htop hupper Fpost hFpostNe hpostWeight hpostDegree hpostFace
  rw [← hmaxRoot] at hnonpositive
  dsimp only at hnonzero
  have hgradeNe : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (Polynomial.rootMultiplicity c
        (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) : ℤ) ≠ 0 := by
    intro hz
    apply hnonzero
    nlinarith [hz]
  omega

/-- A single source-order companion suffices: its exact ramified shear
provides the post-cut witness required by the strict-grade argument. -/
theorem ramifiedCutAut_maxRoot_grade_negative_of_source_companion
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ) (hrpos : 0 < ρ*r)
    (c : ℂ) (P Q F : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ
      (P*F-F*P) = ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ)*(ρ+σ))
    (hPtopDegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0)
    (hmaxRoot : Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r (ramifiedCutExponent l ρ σ)) =
        maxRootMult (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ))) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (Polynomial.rootMultiplicity c
        (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) : ℤ) < 0 := by
  have hPweight : ramifiedWeightDeg l hl ρ σ P = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) P
      ⟨(i,j),hmem,htop⟩
      (fun p hp => hupper p.1 p.2 hp)
  obtain ⟨hGne,hGweight,hGdegree,hGface⟩ :=
    ramifiedCutAut_source_companion l hl ρ σ r hρ hdiv hsum
      c P F hPne hFne hPweight hFweight hdegree hface
  exact ramifiedCutAut_maxRoot_grade_negative_of_source_companions
    l hl ρ σ r i j hρ hdiv hsum hrpos c P Q F
    (ramifiedCutAut l hl ρ σ c F) hcomm hPne hFne hGne
    hmem htop hupper hdegree hface hFweight hPtopDegree
    hOldEnd hmaxRoot hGweight hGdegree hGface

/-- A nonconstant old face selects an actual maximum-multiplicity root;
the transported source companion forces that selected cut endpoint to
have negative grade. The occupied endpoint is retained for the next
Newton-direction step. -/
theorem ramifiedCutAut_exists_maxRoot_negative_grade_of_source_companion
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ) (hrpos : 0 < ρ*r)
    (P Q F : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ
      (P*F-F*P) = ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ)*(ρ+σ))
    (hPtopDegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0) :
    ∃ c : ℂ,
      (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).rootMultiplicity c =
          maxRootMult (ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)) ∧
      ((r - ramifiedCutExponent l ρ σ *
          (maxRootMult (ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)) : ℤ),
         maxRootMult (ramifiedFacePolynomial l hl P r
           (ramifiedCutExponent l ρ σ)))) ∈
        ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P) ∧
      r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) : ℤ) < 0 := by
  have hPweight : ramifiedWeightDeg l hl ρ σ P = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) P
      ⟨(i,j),hmem,htop⟩
      (fun p hp => hupper p.1 p.2 hp)
  have htopFace : ramifiedTopFacePolynomial l hl ρ σ P =
      ramifiedFacePolynomial l hl P r (ramifiedCutExponent l ρ σ) :=
    ramifiedTopFacePolynomial_eq_cutFace l hl ρ σ hρ hdiv P r
      hPweight (fun p hp => by rw [hPweight]; exact hupper p.1 p.2 hp)
  have hcutDegree : 0 < (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).natDegree := by
    rw [← htopFace]
    exact hPtopDegree
  obtain ⟨c,hroot,hmax,hsupport⟩ :=
    ramifiedCutAut_exists_maxRoot_start l hl ρ σ r i j hρ hdiv hsum
      P hmem htop hupper hcutDegree
  have hneg := ramifiedCutAut_maxRoot_grade_negative_of_source_companion
    l hl ρ σ r i j hρ hdiv hsum hrpos c P Q F hcomm hPne hFne
    hmem htop hupper hdegree hface hFweight hPtopDegree hOldEnd hmax
  refine ⟨c,hroot,hmax,hsupport,?_⟩
  rwa [hmax] at hneg

end Dixmier.Weyl
