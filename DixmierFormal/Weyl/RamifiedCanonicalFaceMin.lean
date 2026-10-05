/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFaceStartSum
public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical minimum-order endpoint on the top Newton face
-/

namespace Dixmier.Weyl

set_option maxHeartbeats 1000000

/-- The actual finite PBW support supplies all Laurent upper bounds,
an attained leading weight, and the minimal derivative endpoint on
that leading face. No box or mate-order restriction is introduced. -/
theorem exists_ramified_canonical_face_start
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l)
    (hS : (ramifiedPBWSupport l hl T).Nonempty) :
    ∃ (A : ℤ) (N : ℕ),
      N ∈ (ramifiedPBWCoeffs l hl T).support ∧
      (∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
        ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) ≤ A) ∧
      ρ*ramifiedPBWTopLaurent l hl T N +
        (l : ℤ)*σ*(N : ℤ) = A ∧
      (∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
        ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) = A → N ≤ j) ∧
      ramifiedPBWTopLaurent l hl T N ∈
        ((ramifiedPBWCoeffs l hl T) N).coeff.support ∧
      ramifiedWeightDeg l hl ρ σ T = A := by
  classical
  obtain ⟨A,⟨p,hp,hpA⟩,hupper⟩ :=
    exists_ramifiedPBWSupport_max_weight l hl ρ σ T hS
  let S := ramifiedPBWSupport l hl T
  let F := S.filter fun q => ramifiedWeight l ρ σ q = A
  have hpF : p ∈ F := Finset.mem_filter.mpr ⟨hp,hpA⟩
  have hF : F.Nonempty := ⟨p,hpF⟩
  let O := F.image Prod.snd
  have hO : O.Nonempty := Finset.image_nonempty.mpr hF
  let N : ℕ := O.min' hO
  have hNmem : N ∈ O := Finset.min'_mem O hO
  obtain ⟨q,hqF,hqN⟩ := Finset.mem_image.mp hNmem
  have hqS : q ∈ S := (Finset.mem_filter.mp hqF).1
  have hqA : ramifiedWeight l ρ σ q = A :=
    (Finset.mem_filter.mp hqF).2
  have hqcoeff : ((ramifiedPBWCoeffs l hl T) q.2).coeff q.1 ≠ 0 :=
    (ramifiedPBWSupport_mem_iff l hl T q.1 q.2).mp hqS
  have hNsupport : N ∈ (ramifiedPBWCoeffs l hl T).support := by
    have hqord : q.2 ∈ (ramifiedPBWCoeffs l hl T).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      simp [hz] at hqcoeff
    simpa [← hqN] using hqord
  have hBle : q.1 ≤ ramifiedPBWTopLaurent l hl T N := by
    have hqmem : q.1 ∈
        ((ramifiedPBWCoeffs l hl T) N).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa [← hqN] using hqcoeff
    exact laurentTopExponent_upper _ q.1 hqmem
  have hBmem := ramifiedPBWTopLaurent_mem l hl T N hNsupport
  have hBsupport := ramifiedPBWTopLaurent_support l hl T N hNsupport
  have hBupper := hupper _ hBsupport
  have hqA' : ρ*q.1 + (l : ℤ)*σ*(N : ℤ) = A := by
    simpa [ramifiedWeight, ← hqN] using hqA
  have hBtop : ρ*ramifiedPBWTopLaurent l hl T N +
      (l : ℤ)*σ*(N : ℤ) = A := by
    unfold ramifiedWeight at hBupper
    have : ramifiedPBWTopLaurent l hl T N = q.1 := by
      nlinarith [hBle]
    rw [this]
    exact hqA'
  refine ⟨A,N,hNsupport,?_,hBtop,?_,hBmem,
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ A T
      ⟨p,hp,hpA⟩ hupper⟩
  · intro j hj
    have hs := ramifiedPBWTopLaurent_support l hl T j hj
    exact hupper _ hs
  · intro j hj hjA
    have hs := ramifiedPBWTopLaurent_support l hl T j hj
    have hface : (ramifiedPBWTopLaurent l hl T j,j) ∈ F :=
      Finset.mem_filter.mpr ⟨hs, by simpa [ramifiedWeight] using hjA⟩
    have hjO : j ∈ O := Finset.mem_image.mpr ⟨_,hface,rfl⟩
    exact Finset.min'_le O j hjO

end Dixmier.Weyl
