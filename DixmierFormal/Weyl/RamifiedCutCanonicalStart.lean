/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCanonicalFaceStartPair
public import DixmierFormal.Weyl.RamifiedCutRootEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Identifying the root-selected cut point with the canonical start

The root-multiplicity calculation gives an occupied point on the
sheared old face. Positive first weight makes it the largest Laurent
exponent at its derivative order; the root-order inequality makes it
the minimum-order point of that face.
-/

namespace Dixmier.Weyl

theorem ramifiedCutAut_root_start_is_canonical
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    let U := ramifiedCutAut l hl ρ σ c T
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl T r k)
    ramifiedPBWTopLaurent l hl U m = r-k*(m : ℤ) ∧
      ramifiedWeightDeg l hl ρ σ U = ρ*r ∧
      (∀ n ∈ (ramifiedPBWCoeffs l hl U).support,
        ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl U n,n) =
          ramifiedWeightDeg l hl ρ σ U → m ≤ n) := by
  dsimp only
  let U := ramifiedCutAut l hl ρ σ c T
  let k := ramifiedCutExponent l ρ σ
  let m := Polynomial.rootMultiplicity c
    (ramifiedFacePolynomial l hl T r k)
  obtain ⟨⟨hpoint,hpointWeight⟩,hmin⟩ :=
    ramifiedCutAut_root_start_on_old_face l hl
      ρ σ r i j hρ hdiv hpos c T hmem htop hweight
  have hUupper := ramifiedCutAut_weight_upper l hl ρ σ r
    hρ hdiv hpos c T hweight
  have hmsupp : m ∈ (ramifiedPBWCoeffs l hl U).support := by
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hp := (ramifiedPBWSupport_mem_iff l hl U _ m).mp hpoint
    change ((ramifiedPBWCoeffs l hl U) m).coeff _ ≠ 0 at hp
    rw [hz] at hp
    simp at hp
  have hBle : r-k*(m : ℤ) ≤ ramifiedPBWTopLaurent l hl U m := by
    have hp := (ramifiedPBWSupport_mem_iff l hl U _ m).mp hpoint
    exact laurentTopExponent_upper _ _ (Finsupp.mem_support_iff.mpr hp)
  have hBsupport := ramifiedPBWTopLaurent_support l hl U m hmsupp
  have hBupper := hUupper _ m hBsupport
  have hB : ramifiedPBWTopLaurent l hl U m = r-k*(m : ℤ) := by
    unfold ramifiedWeight at hBupper hpointWeight
    nlinarith [hBle]
  have hDeg : ramifiedWeightDeg l hl ρ σ U = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) U
      ⟨_,hpoint,hpointWeight⟩ (fun p hp => hUupper p.1 p.2 hp)
  refine ⟨hB,hDeg,?_⟩
  intro n hn hnTop
  exact hmin _ n (ramifiedPBWTopLaurent_support l hl U n hn)
    (by rw [hDeg] at hnTop; exact hnTop)

end Dixmier.Weyl
