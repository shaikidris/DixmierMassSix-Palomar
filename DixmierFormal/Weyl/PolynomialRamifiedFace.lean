/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialRamifiedLift
public import DixmierFormal.Weyl.FaceCutMass

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Polynomial face compatibility with the ramified PBW lift

This file identifies the paper's univariate cut polynomial with the
coefficient polynomial on the corresponding scaled ramified face.
-/
namespace Dixmier.Weyl

open MvPolynomial Polynomial

private theorem eval_face_monomial_y (d : Fin 2 →₀ ℕ) :
    (∏ i : Fin 2, (if i = 0 then (1 : ℂ[X]) else Polynomial.X) ^ d i) =
      (Polynomial.X : ℂ[X]) ^ d 1 := by
  simp [Fin.prod_univ_two]

theorem cutPoly_coeff_sum_y (P : A1 ℂ) (ρ σ : ℤ) (j : ℕ) :
    (cutPoly ρ σ P.1).coeff j =
      ∑ d ∈ (leadingForm ρ σ P.1).support,
        if d 1 = j then MvPolynomial.coeff d (leadingForm ρ σ P.1)
        else 0 := by
  unfold cutPoly
  rw [MvPolynomial.eval₂_eq']
  simp_rw [eval_face_monomial_y]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d 1 = j
  · simp [h]
  · have hj : j ≠ d 1 := Ne.symm h
    simp [h, hj]
/-- On a positive-ρ weighted face, a fixed Y exponent determines
the X exponent, so evaluation at x=1 has no collisions. -/
theorem cutPoly_coeff_at_face_point (P : A1 ℂ) (ρ σ : ℤ)
    (i j : ℕ) (hρ : 0 < ρ)
    (hw : (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1) :
    (cutPoly ρ σ P.1).coeff j =
      MvPolynomial.coeff (expo i j) (leadingForm ρ σ P.1) := by
  let F := leadingForm ρ σ P.1
  have hhom : F.IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  rw [cutPoly_coeff_sum_y]
  calc
    (∑ d ∈ F.support,
      if d 1 = j then MvPolynomial.coeff d F else 0) =
        if (expo i j) 1 = j then MvPolynomial.coeff (expo i j) F else 0 := by
      apply Finset.sum_eq_single (expo i j)
      · intro d hd hne
        have hdj : d 1 ≠ j := by
          intro he
          obtain ⟨⟨a,b⟩,rfl⟩ := expo_surjective d
          have hb : b = j := by simpa [expo] using he
          have hweight := hhom (MvPolynomial.mem_support_iff.mp hd)
          rw [expo_weight] at hweight
          change (a : ℤ) * ρ + (b : ℤ) * σ = vDeg ρ σ P.1 at hweight
          have ha : a = i := by
            have hmul : (a : ℤ) * ρ = (i : ℤ) * ρ := by
              rw [hb] at hweight
              omega
            have hcast : (a : ℤ) = (i : ℤ) :=
              (mul_right_cancel₀ (ne_of_gt hρ)) hmul
            exact_mod_cast hcast
          exact hne (by subst a; subst b; rfl)
        simp [hdj]
      · intro hnot
        have hz : MvPolynomial.coeff (expo i j) F = 0 :=
          MvPolynomial.notMem_support_iff.mp hnot
        simp [hz]
    _ = _ := by simp [expo, F]

theorem cutPoly_coeff_at_weight (P : A1 ℂ) (ρ σ : ℤ)
    (i j : ℕ) (hρ : 0 < ρ)
    (hw : (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1) :
    (cutPoly ρ σ P.1).coeff j =
      pbwCoeff (P : Module.End ℂ (Polynomial ℂ)) i j := by
  rw [cutPoly_coeff_at_face_point P ρ σ i j hρ hw]
  rw [leadingForm, MvPolynomial.coeff_weightedHomogeneousComponent]
  simp [expo_weight, hw, symbol_coeff_pbwCoeff]

/-- At every source point of the weighted face, the paper's cut
coefficient is exactly the coefficient on the scaled ramified face. -/
theorem polynomialRamifiedFace_coeff_at_weight
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (i j : ℕ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ))
    (hw : (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1) :
    (ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
        (((l : ℤ) / ρ) * vDeg ρ σ P.1)
        (ramifiedCutExponent l ρ σ)).coeff j =
      (cutPoly ρ σ P.1).coeff j := by
  have hd : ρ * ((l : ℤ) / ρ) = (l : ℤ) :=
    Int.mul_ediv_cancel' hdiv
  have hline :
      (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
        ramifiedCutExponent l ρ σ * (j : ℤ) =
          (l : ℤ) * (i : ℤ) := by
    unfold ramifiedCutExponent
    calc
      ((l : ℤ) / ρ) * vDeg ρ σ P.1 -
          (((l : ℤ) / ρ) * σ) * (j : ℤ) =
        ((l : ℤ) / ρ) *
          ((i : ℤ) * ρ + (j : ℤ) * σ) -
          (((l : ℤ) / ρ) * σ) * (j : ℤ) := by rw [hw]
      _ = (ρ * ((l : ℤ) / ρ)) * (i : ℤ) := by ring
      _ = (l : ℤ) * (i : ℤ) := by rw [hd]
  rw [ramifiedFacePolynomial_coeff, hline,
    polynomialRamifiedLift_pbwCoeff_scaled l hl,
    cutPoly_coeff_at_weight P ρ σ i j hρ hw]

theorem cutPoly_coeff_nonzero_has_face_point (P : A1 ℂ)
    (ρ σ : ℤ) (j : ℕ)
    (h : (cutPoly ρ σ P.1).coeff j ≠ 0) :
    ∃ i : ℕ,
      (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1 := by
  let F := leadingForm ρ σ P.1
  have hjmem : j ∈ (cutPoly ρ σ P.1).support :=
    Polynomial.mem_support_iff.mpr h
  have hsubset := cutPolynomial_support_subset_y_exponents F
  have hjimage : j ∈ F.support.image (fun d => d 1) := by
    apply hsubset
    exact hjmem
  obtain ⟨d,hd,hdj⟩ := Finset.mem_image.mp hjimage
  obtain ⟨⟨i,k⟩,rfl⟩ := expo_surjective d
  have hk : k = j := by simpa [expo] using hdj
  refine ⟨i,?_⟩
  have hhom : F.IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
  rw [expo_weight] at hw
  change (i : ℤ) * ρ + (k : ℤ) * σ = vDeg ρ σ P.1 at hw
  simpa [hk] using hw

theorem polynomialRamifiedFace_coeff_nonzero_has_face_point
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (j : ℕ)
    (hdiv : ρ ∣ (l : ℤ))
    (h : (ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
        (((l : ℤ) / ρ) * vDeg ρ σ P.1)
        (ramifiedCutExponent l ρ σ)).coeff j ≠ 0) :
    ∃ i : ℕ,
      (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1 := by
  let r : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ P.1
  let k : ℤ := ramifiedCutExponent l ρ σ
  have hc : ramifiedPBWCoeff l hl (polynomialRamifiedLift l P)
      (r-k*(j : ℤ)) j ≠ 0 := by
    simpa [r,k, ramifiedFacePolynomial_coeff] using h
  have hmem : (r-k*(j : ℤ),j) ∈
      ramifiedPBWSupport l hl (polynomialRamifiedLift l P) :=
    (ramifiedPBWSupport_mem_iff l hl _ _ j).mpr hc
  obtain ⟨i,hi,_⟩ :=
    (polynomialRamifiedLift_support_iff_scaled l hl P _ j).mp hmem
  refine ⟨i,?_⟩
  have hd : ρ * ((l : ℤ) / ρ) = (l : ℤ) :=
    Int.mul_ediv_cancel' hdiv
  have hline :
      (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
        (((l : ℤ) / ρ) * σ) * (j : ℤ) =
          (l : ℤ) * (i : ℤ) := by
    simpa [r,k,ramifiedCutExponent] using hi
  have hrearr :
      (((l : ℤ) / ρ) * vDeg ρ σ P.1) =
        (((l : ℤ) / ρ) * σ) * (j : ℤ) +
          (l : ℤ) * (i : ℤ) := by omega
  have hprod :
      (l : ℤ) * vDeg ρ σ P.1 =
        (l : ℤ) * ((i : ℤ) * ρ + (j : ℤ) * σ) := by
    calc
      (l : ℤ) * vDeg ρ σ P.1 =
          (ρ * ((l : ℤ) / ρ)) * vDeg ρ σ P.1 := by rw [hd]
      _ = ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by ring
      _ = ρ * (((l : ℤ) / ρ) * σ * (j : ℤ) +
          (l : ℤ) * (i : ℤ)) := by rw [hrearr]
      _ = (ρ * ((l : ℤ) / ρ)) * σ * (j : ℤ) +
          (l : ℤ) * ρ * (i : ℤ) := by ring
      _ = (l : ℤ) * ((i : ℤ) * ρ + (j : ℤ) * σ) := by
        rw [hd]
        ring
  have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  exact ((mul_left_cancel₀ hlz) hprod).symm

/-- The paper's scalar cut polynomial is exactly the coefficient
polynomial on the scaled ramified PBW face. -/
theorem polynomialRamifiedFace_eq_cutPoly
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) :
    ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
      (((l : ℤ) / ρ) * vDeg ρ σ P.1)
      (ramifiedCutExponent l ρ σ) =
        cutPoly ρ σ P.1 := by
  apply Polynomial.ext
  intro j
  by_cases hc : (cutPoly ρ σ P.1).coeff j ≠ 0
  · obtain ⟨i,hw⟩ := cutPoly_coeff_nonzero_has_face_point P ρ σ j hc
    exact polynomialRamifiedFace_coeff_at_weight l hl P ρ σ i j hρ hdiv hw
  · by_cases hr : (ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
        (((l : ℤ) / ρ) * vDeg ρ σ P.1)
        (ramifiedCutExponent l ρ σ)).coeff j ≠ 0
    · obtain ⟨i,hw⟩ :=
        polynomialRamifiedFace_coeff_nonzero_has_face_point
          l hl P ρ σ j hdiv hr
      have heq := polynomialRamifiedFace_coeff_at_weight
        l hl P ρ σ i j hρ hdiv hw
      rw [heq] at hr
      exact (hc hr).elim
    · exact (not_ne_iff.mp hr).trans (not_ne_iff.mp hc).symm

theorem polynomialRamifiedFace_maxRootMult_eq_cutPoly
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) :
    maxRootMult
      (ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
        (((l : ℤ) / ρ) * vDeg ρ σ P.1)
        (ramifiedCutExponent l ρ σ)) =
      maxRootMult (cutPoly ρ σ P.1) := by
  rw [polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]

theorem polynomialRamifiedFace_ne_zero_iff_cutPoly
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) :
    ramifiedFacePolynomial l hl (polynomialRamifiedLift l P)
      (((l : ℤ) / ρ) * vDeg ρ σ P.1)
      (ramifiedCutExponent l ρ σ) ≠ 0 ↔
        cutPoly ρ σ P.1 ≠ 0 := by
  rw [polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]

end Dixmier.Weyl
