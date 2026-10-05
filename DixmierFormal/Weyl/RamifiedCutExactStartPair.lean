/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedReversedFaceStart

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The root-selected start and the unrestricted exact mate after a cut

This is the exact-pair consumer of the root multiplicity calculation.
The mate endpoint is constructed from its actual finite support.
-/

namespace Dixmier.Weyl

theorem ramifiedCutAut_exact_pair_root_start_criterion
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hmpos : 0 < Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r (ramifiedCutExponent l ρ σ))) :
    let P' := ramifiedCutAut l hl ρ σ c P
    let Q' := ramifiedCutAut l hl ρ σ c Q
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl P r k)
    ∃ M : ℕ,
      M ∈ (ramifiedPBWCoeffs l hl Q').support ∧
      ramifiedWeight l ρ σ
        (ramifiedPBWTopLaurent l hl Q' M,M) =
          ramifiedWeightDeg l hl ρ σ Q' ∧
      (∀ b ∈ (ramifiedPBWCoeffs l hl Q').support,
        ramifiedWeight l ρ σ
          (ramifiedPBWTopLaurent l hl Q' b,b) =
            ramifiedWeightDeg l hl ρ σ Q' → M ≤ b) ∧
      (((m : ℂ) * ((ramifiedPBWTopLaurent l hl Q' M : ℤ) : ℂ) -
        (M : ℂ) * ((r-k*(m : ℤ) : ℤ) : ℂ) ≠ 0) ↔
          m+M = 1 ∧
            r-k*(m : ℤ)+ramifiedPBWTopLaurent l hl Q' M = (l : ℤ)) := by
  dsimp only
  let P' := ramifiedCutAut l hl ρ σ c P
  let Q' := ramifiedCutAut l hl ρ σ c Q
  let k := ramifiedCutExponent l ρ σ
  let m := Polynomial.rootMultiplicity c
    (ramifiedFacePolynomial l hl P r k)
  have hQP : Q'*P'-P'*Q' = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  obtain ⟨hB,hPdeg,hPmin⟩ :=
    ramifiedCutAut_root_start_is_canonical l hl
      ρ σ r i j hρ hdiv hpos c P hmem htop hweight
  obtain ⟨⟨hPpoint,hPpointWeight⟩,_⟩ :=
    ramifiedCutAut_root_start_on_old_face l hl
      ρ σ r i j hρ hdiv hpos c P hmem htop hweight
  have hmSupport : m ∈ (ramifiedPBWCoeffs l hl P').support := by
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hp := (ramifiedPBWSupport_mem_iff l hl P' _ m).mp hPpoint
    change ((ramifiedPBWCoeffs l hl P') m).coeff _ ≠ 0 at hp
    rw [hz] at hp
    simp at hp
  obtain ⟨hQS,_⟩ := ramified_exact_pair_support_nonempty
    l hl Q' P' hQP
  obtain ⟨D,M,hM,hQupper,hMtop,hMmin,hMi,hQdeg⟩ :=
    exists_ramified_canonical_face_start l hl ρ σ hρ Q' hQS
  have hPupper : ∀ a ∈ (ramifiedPBWCoeffs l hl P').support,
      ρ*ramifiedPBWTopLaurent l hl P' a +
        (l : ℤ)*σ*(a : ℤ) ≤ ρ*r := by
    intro a ha
    have hs := ramifiedPBWTopLaurent_support l hl P' a ha
    exact ramifiedCutAut_weight_upper l hl ρ σ r hρ hdiv hpos c P
      hweight _ a hs
  have hPtop : ρ*ramifiedPBWTopLaurent l hl P' m +
      (l : ℤ)*σ*(m : ℤ) = ρ*r := by
    rw [hB]
    simpa [ramifiedWeight] using hPpointWeight
  have hPi := ramifiedPBWTopLaurent_mem l hl P' m hmSupport
  have hmEq : m-1+1 = m := Nat.sub_add_cancel hmpos
  have hPmin' : ∀ a ∈ (ramifiedPBWCoeffs l hl P').support,
      ρ*ramifiedPBWTopLaurent l hl P' a +
        (l : ℤ)*σ*(a : ℤ) = ρ*r → m-1+1 ≤ a := by
    intro a ha haTop
    have haTop' : ramifiedWeight l ρ σ
        (ramifiedPBWTopLaurent l hl P' a,a) =
          ramifiedWeightDeg l hl ρ σ P' := by
      rw [hPdeg]
      simpa only [ramifiedWeight] using haTop
    rw [hmEq]
    exact hPmin a ha haTop'
  have hcriterion :=
    ramified_reversed_pair_face_start_nonparallel_iff_constant
      l hl ρ σ hρ hpos P' Q'
      (ramifiedPBWTopLaurent l hl P')
      (ramifiedPBWTopLaurent l hl Q')
      (ρ*r) D (m-1) M hQP
      (by simpa only [hmEq] using hmSupport) hM
      (fun a _ => ramifiedPBWTopLaurent_upper l hl P' a)
      (fun b _ => ramifiedPBWTopLaurent_upper l hl Q' b)
      hPupper hQupper
      hPmin'
      hMmin
      (by simpa only [hmEq] using hPtop)
      hMtop
      (by simpa only [hmEq] using hPi) hMi
  refine ⟨M,hM,?_,?_,?_⟩
  · rw [hQdeg]
    simpa only [ramifiedWeight] using hMtop
  · intro b hb hbTop
    apply hMmin b hb
    rw [hQdeg] at hbTop
    simpa only [ramifiedWeight] using hbTop
  · have hNat : m-1+M = 0 ↔ m+M = 1 := by omega
    have hcast : ((m-1 : ℕ) : ℂ)+1 = (m : ℂ) := by
      exact_mod_cast hmEq
    rw [hcast, hmEq, hB, hNat] at hcriterion
    exact hcriterion

end Dixmier.Weyl
