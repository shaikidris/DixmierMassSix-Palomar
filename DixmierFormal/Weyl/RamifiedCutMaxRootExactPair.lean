/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutExactStartPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Maximum-root selection for an exact cut pair

Two occupied points on the old face make its polynomial nonconstant.
The selected maximum root therefore has positive multiplicity and
supplies every hypothesis of the paired start-endpoint criterion.
-/

namespace Dixmier.Weyl

theorem ramifiedCutAut_maxRoot_exact_pair_start_criterion
    (l : ℕ) (hl : 0 < l) (ρ σ r i₁ i₂ : ℤ) (j₁ j₂ : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (h₁ : (i₁,j₁) ∈ ramifiedPBWSupport l hl P)
    (h₂ : (i₂,j₂) ∈ ramifiedPBWSupport l hl P)
    (hw₁ : ramifiedWeight l ρ σ (i₁,j₁) = ρ*r)
    (hw₂ : ramifiedWeight l ρ σ (i₂,j₂) = ρ*r)
    (hdist : (i₁,j₁) ≠ (i₂,j₂))
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    ∃ (c : ℂ) (M : ℕ),
      (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (ramifiedFacePolynomial l hl P r
        (ramifiedCutExponent l ρ σ)).rootMultiplicity c =
          maxRootMult (ramifiedFacePolynomial l hl P r
            (ramifiedCutExponent l ρ σ)) ∧
      let Q' := ramifiedCutAut l hl ρ σ c Q
      let k := ramifiedCutExponent l ρ σ
      let m := Polynomial.rootMultiplicity c
        (ramifiedFacePolynomial l hl P r k)
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
  let p := ramifiedFacePolynomial l hl P r
    (ramifiedCutExponent l ρ σ)
  have hpdeg : 0 < p.natDegree :=
    ramifiedFacePolynomial_natDegree_pos_of_two_points
      l hl ρ σ r i₁ i₂ j₁ j₂ hρ hdiv P
      h₁ h₂ hw₁ hw₂ hdist
  have hpne : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hpdeg
  obtain ⟨c,hroot,hm,_⟩ :=
    ramifiedCutAut_exists_maxRoot_start_of_two_points
      l hl ρ σ r i₁ i₂ j₁ j₂ hρ hdiv hpos P
      h₁ h₂ hw₁ hw₂ hdist hweight
  have hmpos : 0 < p.rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hpne).mpr hroot
  obtain ⟨M,hM,hQtop,hQmin,hcriterion⟩ :=
    ramifiedCutAut_exact_pair_root_start_criterion
      l hl ρ σ r i₁ j₁ hρ hdiv hpos c P Q
      hcomm h₁ hw₁ hweight hmpos
  exact ⟨c,M,hroot,hm,hM,hQtop,hQmin,hcriterion⟩

end Dixmier.Weyl
