/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeCrossingData
public import DixmierFormal.Weyl.CrossingCutRootCount

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Two occupied terms in the actual small-degree companion -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem smallDegreeCrossing_companion_endpoint
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    H.f1 = H.s+1 ∧ H.f2 = H.rho+1 := by
  have hn := companion_support_recovers_primitive_direction H.companion
    H.rho H.s H.f1 H.f2 _ H.direction H.companionEndProper
    H.companionHomogeneous H.companionBase H.companionEnd
  rw [H.companionStepPrimitive, Nat.div_one, Nat.div_one] at hn
  have hρ := H.rhoPos
  have hf₁ := H.companionEndProper
  omega

theorem smallDegreeCrossing_companion_support
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    H.companion.support = {expo 1 1,expo (H.s+1) (H.rho+1)} := by
  classical
  obtain ⟨hf1,hf2⟩ := smallDegreeCrossing_companion_endpoint P Q H
  have hsρ : H.s < H.rho := by have := H.direction.2; omega
  have hc : Nat.Coprime H.rho H.s := by
    simpa [IsDirection,Nat.Coprime,Int.gcd_def] using H.direction.1
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨k,hk⟩ := companion_support_lattice H.companion H.rho H.s
      H.sPos hsρ hc H.companionHomogeneous e he
    have hbound := H.companionMax e he
    rw [hk] at hbound
    have hbound' : 1+H.s*k ≤ H.s+1 := by simpa [expo,hf1] using hbound
    have hprod : H.s*k ≤ H.s := by omega
    have hkbound : k ≤ 1 := by nlinarith [H.sPos]
    have hkcases : k=0 ∨ k=1 := by omega
    rcases hkcases with hk0 | hk1
    · simp [hk,hk0]
    · simp [hk,hk1,Nat.add_comm]
  · intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact H.companionBase
    · simpa only [hf1,hf2] using H.companionEnd

theorem smallDegreeCrossing_companion_degreeOf_Y
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    H.companion.degreeOf 1 = H.rho+1 := by
  classical
  rw [degreeOf_eq_sup,smallDegreeCrossing_companion_support P Q H]
  simp [expo]

theorem smallDegreeCrossing_scalar_companion_degree
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q)
    (f : Polynomial ℂ) (hf0 : f.eval 0 ≠ 0)
    (hshape : H.companion = (X 0 * X 1) *
      f.eval₂ C (X 0^H.s * X 1^H.rho)) :
    f.natDegree = 1 := by
  have hdegree := crossing_homogeneous_companion_degreeOf_Y H.companion f
    H.rho H.s H.rhoPos hf0 H.companionHomogeneous hshape
  rw [smallDegreeCrossing_companion_degreeOf_Y P Q H] at hdegree
  have hρ := H.rhoPos
  nlinarith

end Dixmier.Weyl
