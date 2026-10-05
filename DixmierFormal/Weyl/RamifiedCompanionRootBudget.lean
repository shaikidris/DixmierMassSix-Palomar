/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionBracketOrder
public import DixmierFormal.Weyl.RamifiedTopCutFace
public import DixmierFormal.Scalar.DerivativeBracketRoots
public import DixmierFormal.Scalar.GeneralRootDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root budget of a general ramified source companion

The source-order leading bracket gives a derivative-bracket identity
for the actual top-face polynomials. Every distinct root of `P`'s
top face is therefore a root of the signed companion top face.
No crossing normal form or operator-order bound is used.
-/

namespace Dixmier.Weyl

open Polynomial Finset

theorem ramified_source_companion_top_face_root_count
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ)) :
    (ramifiedTopFacePolynomial l hl ρ σ P).roots.toFinset.card ≤
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree := by
  have hswap : (-F) * P - P * (-F) = P * F - F * P := by
    apply Subtype.ext
    ext z
    simp
    abel
  have hFneg : -F ≠ 0 := by
    intro hz
    apply hFne
    apply Subtype.ext
    have hval := congrArg Subtype.val hz
    change -(F : Module.End ℂ (LaurentPolynomial ℂ)) = 0 at hval
    exact neg_eq_zero.mp hval
  have hbr : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl ((-F) * P - P * (-F))) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v := by
    intro j v hv
    rw [hswap]
    exact ramified_source_leading_bracket_coeffs
      l hl ρ σ hρ P F hdegree hface j v hv
  have hRweight : ramifiedWeightDeg l hl ρ σ (-F) =
      (l : ℤ) * (ρ + σ) := by
    simpa only [ramifiedWeightDeg_neg] using hFweight
  have hscalar := ramified_top_face_equation_of_bracket_coeffs
    l hl ρ σ hρ hsum P (-F) hPne hFneg hbr hRweight
  have hg : ramifiedTopFacePolynomial l hl ρ σ P ≠ 0 :=
    ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hPne
  have hB : ((ramifiedWeightDeg l hl ρ σ (-F) : ℂ) /
      ((l : ℂ) * (ρ : ℂ))) ≠ 0 := by
    have hA : ramifiedWeightDeg l hl ρ σ (-F) ≠ 0 := by
      rw [hRweight]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
      exact mul_ne_zero hlz (ne_of_gt hsum)
    have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
    have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
    exact div_ne_zero (by exact_mod_cast hA) (mul_ne_zero hlC hρC)
  exact Dixmier.General.derivative_bracket_root_count
    (ramifiedTopFacePolynomial l hl ρ σ (-F))
    (ramifiedTopFacePolynomial l hl ρ σ P)
    ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
      ((l : ℂ) * (ρ : ℂ)))
    ((ramifiedWeightDeg l hl ρ σ (-F) : ℂ) /
      ((l : ℂ) * (ρ : ℂ))) hg hB hscalar

/-- A nonconstant first top face has a complex root. Root containment
therefore makes the source companion's signed top face nonconstant. -/
theorem ramified_source_companion_top_face_degree_pos
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
    (hPdegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    0 < (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree := by
  classical
  let g := ramifiedTopFacePolynomial l hl ρ σ P
  have hg : g ≠ 0 := ne_zero_of_natDegree_gt hPdegree
  obtain ⟨α,hα⟩ := IsAlgClosed.exists_root g
    (natDegree_pos_iff_degree_pos.mp hPdegree).ne'
  have hroot : α ∈ g.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hg).mpr hα)
  have hcard : 0 < g.roots.toFinset.card :=
    Finset.card_pos.mpr ⟨α,hroot⟩
  have hbound : g.roots.toFinset.card ≤
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree := by
    simpa only [g] using ramified_source_companion_top_face_root_count
      l hl ρ σ hρ hsum P F hPne hFne hdegree hface hFweight
  omega

/-- A source-order companion of degree at least two supplies the
integer endpoint relation needed in the selected-cut grade argument.
The degree-one boundary is not covered by this highest-coefficient
cancellation. -/
theorem ramified_source_companion_endpoint_degree_identity
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l) (r : ℤ)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hPweight : ramifiedWeightDeg l hl ρ σ P = ρ*r)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P * F - F * P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P * F - F * P) =
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hPdegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hFdegree : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree) :
    r * ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
      ((l : ℤ) + ramifiedCutExponent l ρ σ) *
        ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree : ℤ) := by
  have hswap : (-F) * P - P * (-F) = P * F - F * P := by
    apply Subtype.ext
    ext z
    simp
    abel
  have hFneg : -F ≠ 0 := by
    intro hz
    apply hFne
    apply Subtype.ext
    have hval := congrArg Subtype.val hz
    change -(F : Module.End ℂ (LaurentPolynomial ℂ)) = 0 at hval
    exact neg_eq_zero.mp hval
  have hbr : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl ((-F) * P - P * (-F))) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v := by
    intro j v hv
    rw [hswap]
    exact ramified_source_leading_bracket_coeffs
      l hl ρ σ hρ P F hdegree hface j v hv
  have hRweight : ramifiedWeightDeg l hl ρ σ (-F) =
      (l : ℤ) * (ρ + σ) := by
    simpa only [ramifiedWeightDeg_neg] using hFweight
  have hscalar := ramified_top_face_equation_of_bracket_coeffs
    l hl ρ σ hρ hsum P (-F) hPne hFneg hbr hRweight
  have hbalance := Dixmier.General.derivative_bracket_top_degree_balance
    (ramifiedTopFacePolynomial l hl ρ σ (-F))
    (ramifiedTopFacePolynomial l hl ρ σ P)
    ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
      ((l : ℂ) * (ρ : ℂ)))
    ((ramifiedWeightDeg l hl ρ σ (-F) : ℂ) /
      ((l : ℂ) * (ρ : ℂ))) hPdegree hFdegree hscalar
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hrawC : (ramifiedWeightDeg l hl ρ σ P : ℂ) *
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℂ) =
      (ramifiedWeightDeg l hl ρ σ (-F) : ℂ) *
        ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree : ℂ) := by
    field_simp at hbalance
    exact hbalance
  have hrawZ : ramifiedWeightDeg l hl ρ σ P *
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
      ramifiedWeightDeg l hl ρ σ (-F) *
        ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree : ℤ) := by
    exact_mod_cast hrawC
  have hcut := ramifiedCutExponent_weight l ρ σ hdiv
  have hcutN := congrArg
    (fun z : ℤ => z *
      ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree : ℤ)) hcut
  rw [hPweight, hRweight] at hrawZ
  nlinarith [hrawZ, hcutN]

/-- The source companion bounds distinct roots of the actual cut-line
polynomial, not merely of an abstract top-face encoding. -/
theorem ramified_source_companion_cut_face_root_count
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ)
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
      (l : ℤ) * (ρ + σ)) :
    (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).roots.toFinset.card ≤
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree := by
  rw [← ramifiedTopFacePolynomial_eq_cutFace l hl ρ σ hρ hdiv
    P r hweight hupper]
  exact ramified_source_companion_top_face_root_count
    l hl ρ σ hρ hsum P F hPne hFne hdegree hface hFweight

/-- The same source companion supplies the numerical maximum-root budget
used by the selected-cut grade inequality. -/
theorem ramified_source_companion_cut_maxRoot_budget
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ)
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
      (l : ℤ) * (ρ + σ)) :
    (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).natDegree ≤
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree *
        maxRootMult (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) := by
  exact complex_polynomial_companion_root_budget _ _
    (ramified_source_companion_cut_face_root_count
      l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight hupper
      hdegree hface hFweight)

/-- In companion degree at least two, the source-order leading bracket
alone supplies both numerical inputs to the nonpositive cut-grade step. -/
theorem ramified_source_companion_cut_grade_nonpositive
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
    (hFdegree : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) ≤ 0 := by
  have hN := ramified_source_companion_cut_maxRoot_budget
    l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight hupper
    hdegree hface hFweight
  have hM := ramified_source_companion_endpoint_degree_identity
    l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight
    hdegree hface hFweight hPdegree hFdegree
  have hfaceEq := ramifiedTopFacePolynomial_eq_cutFace
    l hl ρ σ hρ hdiv P r hweight hupper
  rw [hfaceEq] at hM
  exact ramified_cut_endpoint_grade_nonpositive_of_companion
    l hl ρ σ hρ hdiv hsum r
    (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).natDegree
    (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
    (maxRootMult (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)))
    (by omega) hM hN

/-- The parallel-endpoint branch of G13 Theorem 4.1(2) supplies the
cut-grade bound at every positive companion degree, including degree one.
The exceptional endpoint `(1,1)` branch is separate. -/
theorem ramified_source_companion_parallel_cut_grade_nonpositive
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l) (r u uF : ℤ)
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
    (hPend : ρ*u + (l : ℤ)*σ*
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) = ρ*r)
    (hFend : ρ*uF + (l : ℤ)*σ*
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
        (l : ℤ)*(ρ+σ))
    (hparallel : u*
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree : ℤ) =
      uF*((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ)) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) ≤ 0 := by
  have hN := ramified_source_companion_cut_maxRoot_budget
    l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight hupper
    hdegree hface hFweight
  have hcomp := ramified_companion_endpoint_parallel_degree_identity
    l ρ σ hρ hdiv r u uF
    (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).natDegree
    (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
    hPend hFend hparallel
  exact ramified_cut_endpoint_grade_nonpositive_of_companion
    l hl ρ σ hρ hdiv hsum r
    (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)).natDegree
    (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
    (maxRootMult (ramifiedFacePolynomial l hl P r
      (ramifiedCutExponent l ρ σ)))
    hM hcomp hN

/-- If the companion top face is linear, the root budget forces the
maximum multiplicity to cover the whole cut-face degree. Thus a
negative original ending grade remains negative after the selected
cut. This is the numerical core of G13's exceptional endpoint case. -/
theorem ramified_source_companion_linear_cut_grade_negative
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
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree = 1)
    (hOldEnd : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      (maxRootMult (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)) : ℤ) < 0 := by
  have hbudget := ramified_source_companion_cut_maxRoot_budget
    l hl ρ σ hρ hdiv hsum P F r hPne hFne hweight hupper
    hdegree hface hFweight
  rw [hlinear, one_mul] at hbudget
  have hbudgetZ :
      ((ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) ≤
        (maxRootMult (ramifiedFacePolynomial l hl P r
          (ramifiedCutExponent l ρ σ)) : ℤ) := by
    exact_mod_cast hbudget
  have hkl : (0 : ℤ) < (l : ℤ) + ramifiedCutExponent l ρ σ := by
    have h := ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hsum
    omega
  nlinarith [mul_le_mul_of_nonneg_left hbudgetZ (le_of_lt hkl)]

end Dixmier.Weyl
