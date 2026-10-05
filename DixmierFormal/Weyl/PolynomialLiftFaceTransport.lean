/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Polynomial face transport at arbitrary positive-weight directions

The faithful lift scales weights by its coefficient index. This statement
needs no divisibility of the new direction's first coordinate by that index.
It transfers actual face support after a polynomially recovered shear.
-/

namespace Dixmier.Weyl

theorem polynomialRamifiedLift_weightDeg_scaled_of_pos
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ) (ρ σ : ℤ)
    (hpos : 0 < vDeg ρ σ P.1) :
    ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P) =
      (l : ℤ) * vDeg ρ σ P.1 := by
  obtain ⟨e,he⟩ := MvPolynomial.support_nonempty.mpr
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hpos)
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
  obtain ⟨hs,hw⟩ := polynomialFace_point_source_data P ρ σ i j he
  apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ
    ((l : ℤ) * vDeg ρ σ P.1)
  · refine ⟨((l : ℤ)*(i : ℤ),j), ?_, ?_⟩
    · exact (polynomialRamifiedLift_support_iff_symbol l hl P _ j).mpr ⟨i,rfl,hs⟩
    · rw [polynomialRamifiedLift_weight_scaled,expo_weight,hw]
  · intro p hp
    obtain ⟨k,hk,hs⟩ :=
      (polynomialRamifiedLift_support_iff_symbol l hl P p.1 p.2).mp hp
    have hle := polynomialPBW_weight_le_vDeg P ρ σ k p.2 hs
    rcases p with ⟨u,v⟩
    simp only at hk hs hle
    rw [hk,polynomialRamifiedLift_weight_scaled,expo_weight]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem polynomialRamifiedLift_leading_support_iff
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ) (ρ σ : ℤ)
    (hpos : 0 < vDeg ρ σ P.1) (i j : ℕ) :
    expo i j ∈ (leadingForm ρ σ P.1).support ↔
      ((l : ℤ)*(i : ℤ),j) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) ∧
      ramifiedWeight l ρ σ ((l : ℤ)*(i : ℤ),j) =
        ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P) := by
  rw [polynomialRamifiedLift_weightDeg_scaled_of_pos l hl P ρ σ hpos,
    polynomialRamifiedLift_weight_scaled]
  have hlne : (l : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  constructor
  · intro he
    obtain ⟨hs,hw⟩ := polynomialFace_point_source_data P ρ σ i j he
    refine ⟨(polynomialRamifiedLift_support_iff_symbol l hl P _ j).mpr
      ⟨i,rfl,hs⟩,?_⟩
    rw [expo_weight,hw]
  · rintro ⟨hs,hw⟩
    obtain ⟨k,hk,hkS⟩ :=
      (polynomialRamifiedLift_support_iff_symbol l hl P _ j).mp hs
    have hkiZ : (i : ℤ) = (k : ℤ) := mul_left_cancel₀ hlne hk
    have hki : i = k := by exact_mod_cast hkiZ
    subst k
    change expo i j ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt ρ σ) (vDeg ρ σ P.1) (symbol P.1)).support
    rw [MvPolynomial.support_weightedHomogeneousComponent]
    exact Finset.mem_filter.mpr ⟨hkS,mul_left_cancel₀ hlne hw⟩

end Dixmier.Weyl
