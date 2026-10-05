/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCommonFaceEndpoints

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite candidate slopes for genuine Newton faces

A nonsingleton leading face contains two distinct occupied exponent points.
Their weight equality determines its rational slope. Thus the negative
directions relevant to the G13 direction chain draw their slopes from a
finite set computed directly from the actual PBW support. This does not
yet order the directions or link adjacent faces.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Candidate rational slopes from ordered pairs of occupied PBW exponents. -/
noncomputable def ggvFaceCandidateSlopes (P : A1 ℂ) : Finset ℚ :=
  ((symbol P.1).support.product (symbol P.1).support).image
    (fun p => ((p.2 0 : ℚ) - (p.1 0 : ℚ)) /
      ((p.1 1 : ℚ) - (p.2 1 : ℚ)))

/-- Every genuine leading face with a nonzero first weight has one of the
finitely many slopes determined by pairs in the actual PBW support. -/
theorem ggv_face_slope_mem_candidates
    (P : A1 ℂ) (ρ σ : ℤ)
    (hρ : ρ ≠ 0) (hface : InDir ρ σ P.1) :
    (σ : ℚ) / (ρ : ℚ) ∈ ggvFaceCandidateSlopes P := by
  classical
  obtain ⟨d, e, hd, he, hde⟩ := Finset.one_lt_card_iff.mp hface
  have hdS : d ∈ (symbol P.1).support := by
    have h := hd
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.1
  have heS : e ∈ (symbol P.1).support := by
    have h := he
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.1
  have hdW : Finsupp.weight (wt ρ σ) d = vDeg ρ σ P.1 := by
    have h := hd
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.2
  have heW : Finsupp.weight (wt ρ σ) e = vDeg ρ σ P.1 := by
    have h := he
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.2
  have hcoord : d 1 ≠ e 1 := by
    intro h1
    have hweight : ρ * ((d 0 : ℤ) - e 0) = 0 := by
      simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hdW heW
      have h1z : (d 1 : ℤ) = e 1 := by exact_mod_cast h1
      rw [h1z] at hdW
      nlinarith [hdW, heW]
    have h0 : d 0 = e 0 := by
      have hz : ((d 0 : ℤ) - e 0) = 0 :=
        (mul_eq_zero.mp hweight).resolve_left hρ
      exact_mod_cast (sub_eq_zero.mp hz)
    apply hde
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hden : ((d 1 : ℚ) - (e 1 : ℚ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hcoord)
  have hρQ : (ρ : ℚ) ≠ 0 := by exact_mod_cast hρ
  have hweight :
      (ρ : ℚ) * ((d 0 : ℚ) - e 0) +
        (σ : ℚ) * ((d 1 : ℚ) - e 1) = 0 := by
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hdW heW
    exact_mod_cast (show ρ * ((d 0 : ℤ) - e 0) +
      σ * ((d 1 : ℤ) - e 1) = 0 by nlinarith [hdW, heW])
  apply Finset.mem_image.mpr
  refine ⟨(d,e), Finset.mem_product.mpr ⟨hdS,heS⟩, ?_⟩
  dsimp
  apply (div_eq_div_iff hden hρQ).mpr
  nlinarith [hweight]

/-- The set of slopes of genuine negative faces of a fixed operator is finite. -/
theorem ggv_negative_face_slopes_finite (P : A1 ℂ) :
    {t : ℚ | ∃ ρ σ : ℤ, 0 < ρ ∧ σ < 0 ∧
      InDir ρ σ P.1 ∧ t = (σ : ℚ) / (ρ : ℚ)}.Finite := by
  apply (ggvFaceCandidateSlopes P).finite_toSet.subset
  rintro t ⟨ρ,σ,hρ,_,hface,rfl⟩
  exact ggv_face_slope_mem_candidates P ρ σ (ne_of_gt hρ) hface

/-- A primitive negative normal with positive first coordinate is uniquely
determined by its rational slope. -/
theorem ggv_primitive_negative_normal_unique
    (ρ σ ρ' σ' : ℤ)
    (hdir : IsDirection ρ σ) (hdir' : IsDirection ρ' σ')
    (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hslope : (σ : ℚ) / (ρ : ℚ) = (σ' : ℚ) / (ρ' : ℚ)) :
    ρ = ρ' ∧ σ = σ' := by
  have hρQ : (ρ : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hρ'Q : (ρ' : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ')
  have hcrossQ : (σ : ℚ) * ρ' = (σ' : ℚ) * ρ :=
    (div_eq_div_iff hρQ hρ'Q).mp hslope
  have hcross : σ * ρ' = σ' * ρ := by exact_mod_cast hcrossQ
  have hcop : IsCoprime ρ σ := Int.isCoprime_iff_gcd_eq_one.mpr hdir.1
  have hcop' : IsCoprime ρ' σ' := Int.isCoprime_iff_gcd_eq_one.mpr hdir'.1
  have hdiv : ρ ∣ ρ' := by
    apply hcop.dvd_of_dvd_mul_left
    refine ⟨σ', ?_⟩
    exact hcross.trans (mul_comm σ' ρ)
  have hdiv' : ρ' ∣ ρ := by
    apply hcop'.dvd_of_dvd_mul_left
    refine ⟨σ, ?_⟩
    exact hcross.symm.trans (mul_comm σ ρ')
  have hρeq : ρ = ρ' := Int.dvd_antisymm (le_of_lt hρ) (le_of_lt hρ') hdiv hdiv'
  constructor
  · exact hρeq
  · rw [hρeq] at hcross
    have hz : (σ - σ') * ρ' = 0 := by linear_combination hcross
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hρ'))

/-- Primitive strict negative face directions, not only their slopes, form
a finite set for each actual polynomial Weyl operator. -/
theorem ggv_negative_primitive_face_directions_finite (P : A1 ℂ) :
    {v : ℤ × ℤ | IsDirection v.1 v.2 ∧ 0 < v.1 ∧ v.2 < 0 ∧
      InDir v.1 v.2 P.1}.Finite := by
  let S : Set (ℤ × ℤ) :=
    {v | IsDirection v.1 v.2 ∧ 0 < v.1 ∧ v.2 < 0 ∧ InDir v.1 v.2 P.1}
  let slope : (ℤ × ℤ) → ℚ := fun v => (v.2 : ℚ) / (v.1 : ℚ)
  have hImage : (slope '' S).Finite :=
    (ggv_negative_face_slopes_finite P).subset (by
      rintro t ⟨⟨ρ,σ⟩,⟨hdir,hρ,hσ,hface⟩,rfl⟩
      exact ⟨ρ,σ,hρ,hσ,hface,rfl⟩)
  have hInj : S.InjOn slope := by
    intro v hv w hw hslope
    rcases v with ⟨ρ,σ⟩
    rcases w with ⟨ρ',σ'⟩
    change IsDirection ρ σ ∧ 0 < ρ ∧ σ < 0 ∧ InDir ρ σ P.1 at hv
    change IsDirection ρ' σ' ∧ 0 < ρ' ∧ σ' < 0 ∧ InDir ρ' σ' P.1 at hw
    rcases hv with ⟨hdir,hρ,_,_⟩
    rcases hw with ⟨hdir',hρ',_,_⟩
    obtain ⟨h₁,h₂⟩ :=
      ggv_primitive_negative_normal_unique ρ σ ρ' σ' hdir hdir' hρ hρ' hslope
    exact Prod.ext h₁ h₂
  exact Set.Finite.of_finite_image hImage hInj

end Dixmier.Weyl
