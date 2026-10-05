/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerLeadingBracket
public import DixmierFormal.Weyl.NewtonEndpointCones

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Negative mate endpoint at the G13 corner

This completes the grade-sign transfer in the first stage of G13
Proposition 5.6. The descending cut of the second stage remains separate.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- On a positive-sum Newton face with positive first weight, the
diagonal grade and the perpendicular supporting functional order its
points in the same direction. This identifies the endpoint selected by
the generic Poisson endpoint theorem with the specified G13 corner. -/
theorem face_grade_order_implies_perp_order
    (ρ σ : ℤ) (u v : Fin 2 →₀ ℕ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (hweight : Finsupp.weight (wt ρ σ) u =
      Finsupp.weight (wt ρ σ) v)
    (hgrade : grade u ≤ grade v) :
    Finsupp.weight (perpWeight (wt ρ σ)) u ≤
      Finsupp.weight (perpWeight (wt ρ σ)) v := by
  have hw : ρ * ((u 0 : ℤ) - v 0) + σ * ((u 1 : ℤ) - v 1) = 0 := by
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hweight
    nlinarith [hweight]
  have hg : (u 0 : ℤ) - u 1 ≤ (v 0 : ℤ) - v 1 := by
    simpa [grade] using hgrade
  have hy : (v 1 : ℤ) ≤ u 1 := by
    have hkey : ρ * (((u 0 : ℤ) - u 1) - ((v 0 : ℤ) - v 1)) =
        -(ρ + σ) * ((u 1 : ℤ) - v 1) := by nlinarith [hw]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρ) (by omega :
      ((u 0 : ℤ) - u 1) - ((v 0 : ℤ) - v 1) ≤ 0)]
  have hperp :
      ρ * (σ * ((v 0 : ℤ) - u 0) - ρ * ((v 1 : ℤ) - u 1)) =
        (ρ*ρ + σ*σ) * ((u 1 : ℤ) - v 1) := by
    have hσ := congrArg (fun z : ℤ => σ*z) hw
    nlinarith [hσ]
  have hcoef : 0 ≤ ρ*ρ + σ*σ := by
    nlinarith [sq_nonneg ρ, sq_nonneg σ]
  have hprod := mul_nonneg hcoef (show 0 ≤ (u 1 : ℤ) - v 1 by omega)
  simp [perpWeight, wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at *
  nlinarith [hperp, hprod]

/-- The specified minimum-grade endpoint, rather than an arbitrary
negative-grade point in the positive support cone, is collinear with an
actual mate endpoint. This is the endpoint selection used in the
descending-cut proof of G13 Proposition 5.6. -/
theorem face_min_grade_poisson_mate_endpoint_collinear
    (ρ σ degreeP degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ) (corner : Fin 2 →₀ ℕ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (hpdeg : ∀ x ∈ p.support,
      Finsupp.weight (wt ρ σ) x = degreeP)
    (hqdeg : ∀ x ∈ q.support,
      Finsupp.weight (wt ρ σ) x = degreeQ)
    (hpne : p ≠ 0) (hqne : q ≠ 0)
    (hbr : poisson p q = 0)
    (hc : corner ∈ p.support)
    (hcmin : ∀ x ∈ p.support, grade corner ≤ grade x) :
    ∃ e ∈ q.support,
      (e 1 : ℂ) * (corner 0 : ℂ) -
        (e 0 : ℂ) * (corner 1 : ℂ) = 0 ∧
      (∀ x ∈ q.support,
        Finsupp.weight (perpWeight (wt ρ σ)) e ≤
          Finsupp.weight (perpWeight (wt ρ σ)) x) := by
  have hwnz : (wt ρ σ) 0 ≠ 0 ∨ (wt ρ σ) 1 ≠ 0 := by
    left
    simpa [wt] using (ne_of_gt hρ)
  obtain ⟨dp,dm,ep,em,hdp,hdm,hep,hem,hdpmax,hdmmin,
    hepmax,hemmin,_,hparallel⟩ :=
    poisson_homogeneous_support_endpoints_collinear
      (wt ρ σ) degreeP degreeQ p q hwnz hpdeg hqdeg
      hpne hqne hbr
  have hcperp : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight (wt ρ σ)) corner ≤
        Finsupp.weight (perpWeight (wt ρ σ)) x := by
    intro x hx
    exact face_grade_order_implies_perp_order ρ σ corner x
      hρ hsum ((hpdeg corner hc).trans (hpdeg x hx).symm)
      (hcmin x hx)
  have hperpEq :
      Finsupp.weight (perpWeight (wt ρ σ)) corner =
        Finsupp.weight (perpWeight (wt ρ σ)) dm := by
    exact le_antisymm (hcperp dm hdm) (hdmmin corner hc)
  have hcornerEq : corner = dm :=
    exponent_eq_of_weights_eq_of_perp_eq (wt ρ σ) hwnz
      ((hpdeg corner hc).trans (hpdeg dm hdm).symm) hperpEq
  subst dm
  refine ⟨em,hem,?_,hemmin⟩
  linear_combination -hparallel

set_option maxHeartbeats 800000

/-- The source-facing endpoint package at the normalized polynomial
corner. The selected mate point is collinear with the *specified*
corner, and its grade is negative. The ramified cut remains separate. -/
theorem corner_actual_mate_endpoint_collinear_negative
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ)
    (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection ρ σ) (hσ : σ ≤ 0)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hQpos : 0 < vDeg ρ σ Q.1)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hmin : ∀ x ∈ (leadingForm ρ σ P.1).support,
      grade (expo a b) ≤ grade x)
    (hratio : vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : (a : ℚ) / d = h - 1)
    (hb : (b : ℚ) / d = h) :
    ∃ e ∈ (leadingForm ρ σ Q.1).support,
      grade e < 0 ∧
      (e 1 : ℂ) * (a : ℂ) - (e 0 : ℂ) * (b : ℂ) = 0 := by
  let p := leadingForm ρ σ P.1
  let q := leadingForm ρ σ Q.1
  have hρ : 0 < ρ := by have := hdir.2; omega
  have hbr : poisson p q = 0 := by
    have h := corner_leading_poisson_zero_of_normalized
      P Q ρ σ a b n d h hpair hdir hPpos hend hratio hd hn hh ha hb
    have hanti : poisson p q = -poisson q p := by unfold poisson; ring
    rw [hanti]
    simpa [p,q] using congrArg Neg.neg h
  have hpne : p ≠ 0 := leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos
  have hqne : q ≠ 0 := leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos
  have hphom : p.IsWeightedHomogeneous (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hqhom : q.IsWeightedHomogeneous (wt ρ σ) (vDeg ρ σ Q.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt ρ σ) (n := vDeg ρ σ Q.1)
  obtain ⟨e,he,hcol,_⟩ := face_min_grade_poisson_mate_endpoint_collinear
    ρ σ (vDeg ρ σ P.1) (vDeg ρ σ Q.1) p q (expo a b)
    hρ hdir.2
    (fun x hx => hphom (MvPolynomial.mem_support_iff.mp hx))
    (fun x hx => hqhom (MvPolynomial.mem_support_iff.mp hx))
    hpne hqne hbr hend hmin
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
  have haQ : (a : ℚ) = (d : ℚ) * ((h : ℚ) - 1) := by
    apply (div_eq_iff hdQ).mp at ha
    nlinarith [ha]
  have hbQ : (b : ℚ) = (d : ℚ) * (h : ℚ) := by
    apply (div_eq_iff hdQ).mp at hb
    nlinarith [hb]
  have haZ : (a : ℤ) = (d : ℤ) * ((h : ℤ) - 1) := by exact_mod_cast haQ
  have hbZ : (b : ℤ) = (d : ℤ) * (h : ℤ) := by exact_mod_cast hbQ
  have hdZ : (0 : ℤ) < d := by exact_mod_cast (by omega : 0 < d)
  have hhZ : (0 : ℤ) < (h : ℤ) - 1 := by
    have hhZ' : (2 : ℤ) ≤ h := by exact_mod_cast hh
    omega
  have haPos : (0 : ℤ) < a := by nlinarith [mul_pos hdZ hhZ]
  have hab : (a : ℤ) < b := by nlinarith [haZ,hbZ]
  have hweightP : 0 < ρ * (a : ℤ) + σ * (b : ℤ) := by
    have hw := hphom (MvPolynomial.mem_support_iff.mp hend)
    rw [expo_weight] at hw
    nlinarith [hw]
  have hweightQ : 0 < ρ * (e 0 : ℤ) + σ * (e 1 : ℤ) := by
    have hw := hqhom (MvPolynomial.mem_support_iff.mp he)
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hw
    nlinarith [hw]
  have hcolZ : (a : ℤ) * (e 1 : ℤ) = (b : ℤ) * (e 0 : ℤ) := by
    simp [expo] at hcol
    have hcol' : (a : ℂ) * (e 1 : ℂ) = (b : ℂ) * (e 0 : ℂ) := by
      calc
        (a : ℂ) * (e 1 : ℂ) = (e 1 : ℂ) * (a : ℂ) := mul_comm _ _
        _ = (e 0 : ℂ) * (b : ℂ) := sub_eq_zero.mp hcol
        _ = (b : ℂ) * (e 0 : ℂ) := mul_comm _ _
    exact_mod_cast hcol'
  have hneg := corner_proportional_mate_grade_negative
    ρ σ a b (e 0) (e 1) haPos hweightQ hweightP hab hcolZ
  exact ⟨e,he,by simpa [grade] using hneg,by simpa [expo] using hcol⟩

/-- Equal positive cones of two finite polynomial supports transfer the
existence of a negative-grade support monomial. -/
theorem negative_grade_support_of_equal_cones
    (p q : MvPolynomial (Fin 2) ℂ)
    (hcone : positiveScalarCone
        (convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))) =
      positiveScalarCone
        (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))))
    (d : Fin 2 →₀ ℕ) (hd : d ∈ p.support) (hneg : grade d < 0) :
    ∃ e ∈ q.support, grade e < 0 := by
  by_contra hnone
  have hnonneg : ∀ e ∈ q.support, 0 ≤ grade e := by
    intro e he
    by_contra h
    exact hnone ⟨e, he, by omega⟩
  have hsupport : exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)) ⊆
      {z : ℝ × ℝ | 0 ≤ z.1 - z.2} := by
    rintro z ⟨e, he, rfl⟩
    have h := hnonneg e he
    change 0 ≤ (e 0 : ℝ) - (e 1 : ℝ)
    simpa [grade] using (show (0 : ℝ) ≤ (e 0 : ℝ) - (e 1 : ℝ) by
      exact_mod_cast (show (0 : ℤ) ≤ (e 0 : ℤ) - (e 1 : ℤ) by simpa [grade] using h))
  have hhull : convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ))) ⊆
      {z : ℝ × ℝ | 0 ≤ z.1 - z.2} :=
    convexHull_min hsupport (convex_halfSpace_ge IsLinearMap.isLinearMap_sub 0)
  have hconeNonneg : positiveScalarCone
      (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))) ⊆
      {z : ℝ × ℝ | 0 ≤ z.1 - z.2} := by
    rintro z ⟨r, hr, y, hy, rfl⟩
    change 0 ≤ r * y.1 - r * y.2
    have hy' := hhull hy
    change 0 ≤ y.1 - y.2 at hy'
    nlinarith [mul_nonneg hr hy']
  have hdHull : exponentPoint d ∈
      convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ))) :=
    subset_convexHull ℝ _ ⟨d, hd, rfl⟩
  have hdCone : exponentPoint d ∈ positiveScalarCone
      (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))) := by
    rw [← hcone]
    exact ⟨1, by norm_num, exponentPoint d, hdHull, by simp⟩
  have hnonnegD := hconeNonneg hdCone
  change 0 ≤ (d 0 : ℝ) - (d 1 : ℝ) at hnonnegD
  have hnegReal : (d 0 : ℝ) - (d 1 : ℝ) < 0 := by
    exact_mod_cast (show (d 0 : ℤ) - (d 1 : ℤ) < 0 by simpa [grade] using hneg)
  linarith

/-- At the normalized corner, the mate's ending face also has negative
grade. The support point returned is minimal in grade on that face. -/
theorem corner_mate_end_grade_negative
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ)
    (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection ρ σ)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hQpos : 0 < vDeg ρ σ Q.1)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hratio : vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : (a : ℚ) / d = h - 1)
    (hb : (b : ℚ) / d = h) :
    ∃ e ∈ (leadingForm ρ σ Q.1).support,
      grade e < 0 ∧
        ∀ f ∈ (leadingForm ρ σ Q.1).support, grade e ≤ grade f := by
  let p := leadingForm ρ σ P.1
  let q := leadingForm ρ σ Q.1
  have hbr : poisson q p = 0 :=
    corner_leading_poisson_zero_of_normalized P Q ρ σ a b n d h
      hpair hdir hPpos hend hratio hd hn hh ha hb
  have hpne : p ≠ 0 := leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos
  have hqne : q ≠ 0 := leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos
  have hphom : p.IsWeightedHomogeneous (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hqhom : q.IsWeightedHomogeneous (wt ρ σ) (vDeg ρ σ Q.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt ρ σ) (n := vDeg ρ σ Q.1)
  have hwnz : (wt ρ σ) 0 ≠ 0 ∨ (wt ρ σ) 1 ≠ 0 := by
    have := hdir.2
    by_cases hρ : ρ = 0
    · right
      simpa [wt] using (show σ ≠ 0 by omega)
    · left
      simpa [wt] using hρ
  have hcone := poisson_homogeneous_support_cones_equal_of_nonzero_degrees
    (wt ρ σ) (vDeg ρ σ Q.1) (vDeg ρ σ P.1) q p hwnz
    (fun e he => hqhom (MvPolynomial.mem_support_iff.mp he))
    (fun e he => hphom (MvPolynomial.mem_support_iff.mp he))
    hqne hpne hbr (by omega) (by omega)
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
  have haQ : (a : ℚ) = (d : ℚ) * ((h : ℚ) - 1) := by
    apply (div_eq_iff hdQ).mp at ha
    nlinarith [ha]
  have hbQ : (b : ℚ) = (d : ℚ) * (h : ℚ) := by
    apply (div_eq_iff hdQ).mp at hb
    nlinarith [hb]
  have haZ : (a : ℤ) = (d : ℤ) * ((h : ℤ) - 1) := by exact_mod_cast haQ
  have hbZ : (b : ℤ) = (d : ℤ) * (h : ℤ) := by exact_mod_cast hbQ
  have hgrade : grade (expo a b) < 0 := by
    simp [grade, expo]
    nlinarith [haZ, hbZ]
  obtain ⟨e, he, heNeg⟩ := negative_grade_support_of_equal_cones
    p q hcone.symm (expo a b) hend hgrade
  obtain ⟨emin, hminMem, hmin⟩ := q.support.exists_min_image grade
    (MvPolynomial.support_nonempty.mpr hqne)
  exact ⟨emin, hminMem, lt_of_le_of_lt (hmin e he) heNeg, hmin⟩

/-- The complete first stage of G13 Proposition 5.6 for polynomial Weyl
pairs: zero leading bracket and negative ending grades for both members.
The descending-cut contradiction is not part of this theorem. -/
theorem corner_first_stage
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ)
    (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection ρ σ)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hQpos : 0 < vDeg ρ σ Q.1)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hratio : vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : (a : ℚ) / d = h - 1)
    (hb : (b : ℚ) / d = h) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 0 ∧
      grade (expo a b) < 0 ∧
      ∃ e ∈ (leadingForm ρ σ Q.1).support,
        grade e < 0 ∧
          ∀ f ∈ (leadingForm ρ σ Q.1).support, grade e ≤ grade f := by
  have hbr := corner_leading_poisson_zero_of_normalized P Q ρ σ a b n d h
    hpair hdir hPpos hend hratio hd hn hh ha hb
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
  have haQ : (a : ℚ) = (d : ℚ) * ((h : ℚ) - 1) := by
    apply (div_eq_iff hdQ).mp at ha
    nlinarith [ha]
  have hbQ : (b : ℚ) = (d : ℚ) * (h : ℚ) := by
    apply (div_eq_iff hdQ).mp at hb
    nlinarith [hb]
  have haZ : (a : ℤ) = (d : ℤ) * ((h : ℤ) - 1) := by exact_mod_cast haQ
  have hbZ : (b : ℤ) = (d : ℤ) * (h : ℤ) := by exact_mod_cast hbQ
  have hPneg : grade (expo a b) < 0 := by
    simp [grade, expo]
    nlinarith [haZ, hbZ]
  exact ⟨hbr, hPneg,
    corner_mate_end_grade_negative P Q ρ σ a b n d h
      hpair hdir hPpos hQpos hend hratio hd hn hh ha hb⟩

end Dixmier.Weyl
