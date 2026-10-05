/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedTopCutFace
public import DixmierFormal.Weyl.RamifiedShearPBWSum

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical top faces under an exact ramified shear

For any attained old Newton weight, the shear preserves that weight and
translates the entire canonical top-face polynomial. This applies to a
source-order commutator as well as to either member of an exact pair.
-/

namespace Dixmier.Weyl

@[simp] theorem ramifiedTopFacePolynomial_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) :
    ramifiedTopFacePolynomial l hl ρ σ (0 : ramifiedOperatorAlgebra l) = 0 := by
  have hcoeff : ramifiedPBWCoeffs l hl (0 : ramifiedOperatorAlgebra l) = 0 := by
    apply ramifiedPBWCoeffs_eq_of_eval l hl 0 0
    simp [ramifiedNormalEval]
  ext j
  simp [ramifiedTopFacePolynomial_coeff, hcoeff]

theorem ramifiedCutAut_topFace_eq_translate
    (l : ℕ) (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (c : ℂ) (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ ρ*r) :
    ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c T) = ρ*r ∧
    ramifiedTopFacePolynomial l hl ρ σ (ramifiedCutAut l hl ρ σ c T) =
      (ramifiedTopFacePolynomial l hl ρ σ T).comp
        (Polynomial.X + Polynomial.C c) := by
  have hTweight : ramifiedWeightDeg l hl ρ σ T = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r) T
      ⟨(i,j),hmem,htop⟩ hupper
  obtain ⟨⟨u,n,hpoint,hpointWeight⟩,hcutUpper⟩ :=
    ramifiedCutAut_preserves_max_weight_data l hl ρ σ r i j
      hρ hdiv hsum c T hmem htop (fun u n h => hupper (u,n) h)
  have hcutWeight : ramifiedWeightDeg l hl ρ σ
      (ramifiedCutAut l hl ρ σ c T) = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r)
      (ramifiedCutAut l hl ρ σ c T)
      ⟨(u,n),hpoint,hpointWeight⟩
      (fun p hp => hcutUpper p.1 p.2 hp)
  have hTface := ramifiedTopFacePolynomial_eq_cutFace
    l hl ρ σ hρ hdiv T r hTweight
    (fun p hp => by rw [hTweight]; exact hupper p hp)
  have hcutFace := ramifiedTopFacePolynomial_eq_cutFace
    l hl ρ σ hρ hdiv (ramifiedCutAut l hl ρ σ c T) r hcutWeight
    (fun p hp => by rw [hcutWeight]; exact hcutUpper p.1 p.2 hp)
  have htranslate := ramifiedCutAut_face_eq_translate_of_weight_upper
    l hl ρ σ r hρ hdiv hsum c T
      (fun u n h => hupper (u,n) h)
  refine ⟨hcutWeight, ?_⟩
  rw [hTface, hcutFace]
  exact htranslate

/-- An attained maximal weight is automatic for every nonzero finite
ramified operator. This form is convenient for transporting a source
companion and its leading bracket through the same shear. -/
theorem ramifiedCutAut_topFace_eq_translate_of_weight
    (l : ℕ) (hl : 0 < l) (ρ σ r : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (c : ℂ) (T : ramifiedOperatorAlgebra l)
    (hTne : T ≠ 0)
    (hweight : ramifiedWeightDeg l hl ρ σ T = ρ*r) :
    ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c T) = ρ*r ∧
    ramifiedTopFacePolynomial l hl ρ σ (ramifiedCutAut l hl ρ σ c T) =
      (ramifiedTopFacePolynomial l hl ρ σ T).comp
        (Polynomial.X + Polynomial.C c) := by
  have hS := ramifiedPBWSupport_nonempty_of_ne_zero l hl T hTne
  obtain ⟨A,N,hN,hbound,hNtop,_,_,hA⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ T hS
  have hAeq : A = ρ*r := hA.symm.trans hweight
  have hpoint := ramifiedPBWTopLaurent_support l hl T N hN
  have hpointWeight : ramifiedWeight l ρ σ
      (ramifiedPBWTopLaurent l hl T N,N) = ρ*r := by
    simpa [ramifiedWeight,hAeq] using hNtop
  have hupper : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ ρ*r := by
    intro p hp
    have hcoeff := (ramifiedPBWSupport_mem_iff l hl T p.1 p.2).mp hp
    have hj : p.2 ∈ (ramifiedPBWCoeffs l hl T).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      simp [ramifiedPBWCoeff,hz] at hcoeff
    have hpLaurent : p.1 ≤ ramifiedPBWTopLaurent l hl T p.2 := by
      apply laurentTopExponent_upper
      exact Finsupp.mem_support_iff.mpr hcoeff
    have hjbound := hbound p.2 hj
    rw [hAeq] at hjbound
    have hgap : 0 ≤ ρ *
        (ramifiedPBWTopLaurent l hl T p.2 - p.1) :=
      mul_nonneg (le_of_lt hρ) (sub_nonneg.mpr hpLaurent)
    dsimp [ramifiedWeight]
    nlinarith [hjbound,hgap]
  exact ramifiedCutAut_topFace_eq_translate l hl ρ σ r
    (ramifiedPBWTopLaurent l hl T N) N hρ hdiv hsum c T
    hpoint hpointWeight hupper

/-- The exact shear transports one source-order companion to another.
This is an operator statement: the commutator, its attained weight, and
its entire leading polynomial are transported together. -/
theorem ramifiedCutAut_source_companion
    (l : ℕ) (hl : 0 < l) (ρ σ r : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (c : ℂ) (P F : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
    (hPweight : ramifiedWeightDeg l hl ρ σ P = ρ*r)
    (hFweight : ramifiedWeightDeg l hl ρ σ F = (l : ℤ)*(ρ+σ))
    (hHweight : ramifiedWeightDeg l hl ρ σ (P*F-F*P) =
      ramifiedWeightDeg l hl ρ σ P)
    (hHface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P) =
      ramifiedTopFacePolynomial l hl ρ σ P) :
    let U := ramifiedCutAut l hl ρ σ c P
    let G := ramifiedCutAut l hl ρ σ c F
    G ≠ 0 ∧ ramifiedWeightDeg l hl ρ σ G = (l : ℤ)*(ρ+σ) ∧
      ramifiedWeightDeg l hl ρ σ (U*G-G*U) =
        ramifiedWeightDeg l hl ρ σ U ∧
      ramifiedTopFacePolynomial l hl ρ σ (U*G-G*U) =
        ramifiedTopFacePolynomial l hl ρ σ U := by
  dsimp only
  have hFfactor : ρ * (((l : ℤ) / ρ) * (ρ+σ)) =
      (l : ℤ)*(ρ+σ) := by
    calc
      _ = (ρ * ((l : ℤ) / ρ)) * (ρ+σ) := by ring
      _ = (l : ℤ)*(ρ+σ) := by rw [Int.mul_ediv_cancel' hdiv]
  have hFweight' : ramifiedWeightDeg l hl ρ σ F =
      ρ * (((l : ℤ) / ρ) * (ρ+σ)) := by
    rw [hFfactor]
    exact hFweight
  obtain ⟨hUw,hUf⟩ := ramifiedCutAut_topFace_eq_translate_of_weight
    l hl ρ σ r hρ hdiv hsum c P hPne hPweight
  obtain ⟨hGw,_⟩ := ramifiedCutAut_topFace_eq_translate_of_weight
    l hl ρ σ (((l : ℤ) / ρ) * (ρ+σ))
    hρ hdiv hsum c F hFne hFweight'
  have hHweight' : ramifiedWeightDeg l hl ρ σ (P*F-F*P) = ρ*r := by
    rw [hHweight]
    exact hPweight
  have hHne : P*F-F*P ≠ 0 := by
    intro hz
    have hPfaceNe := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hPne
    apply hPfaceNe
    rw [← hHface, hz, ramifiedTopFacePolynomial_zero]
  obtain ⟨hHw,hHf⟩ := ramifiedCutAut_topFace_eq_translate_of_weight
    l hl ρ σ r hρ hdiv hsum c (P*F-F*P) hHne hHweight'
  have hcomm : ramifiedCutAut l hl ρ σ c (P*F-F*P) =
      ramifiedCutAut l hl ρ σ c P * ramifiedCutAut l hl ρ σ c F -
      ramifiedCutAut l hl ρ σ c F * ramifiedCutAut l hl ρ σ c P := by
    rw [← map_mul, ← map_mul]
    exact (map_sub (ramifiedCutAut l hl ρ σ c) (P*F) (F*P))
  have hGne : ramifiedCutAut l hl ρ σ c F ≠ 0 := by
    simpa using (ramifiedCutAut l hl ρ σ c).injective.ne hFne
  refine ⟨hGne,
    hGw.trans hFfactor, ?_, ?_⟩
  · rw [← hcomm, hHw, hUw]
  · rw [← hcomm, hHf, hHface, hUf]

end Dixmier.Weyl
