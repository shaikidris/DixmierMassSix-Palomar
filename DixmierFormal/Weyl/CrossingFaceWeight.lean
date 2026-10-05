/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingFaceCutPolynomial

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
/-!
# Weight of an explicit crossing face

A monomial of a leading face has weight equal to the operator's weighted
degree. The proved starting monomial therefore fixes that degree to `eρ`.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Every support monomial of a leading face has the weighted degree of its
operator. -/
theorem weight_of_mem_leadingForm
    (T : A1 ℂ) (ρ σ : ℤ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (leadingForm ρ σ T.1).support) :
    Finsupp.weight (wt ρ σ) d = vDeg ρ σ T.1 := by
  change d ∈ (MvPolynomial.weightedHomogeneousComponent
    (wt ρ σ) (vDeg ρ σ T.1) (symbol T.1)).support at hd
  rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
  exact (Finset.mem_filter.mp hd).2

/-- The starting monomial of an explicit pure-power face fixes the operator's
weighted degree to `eρ`. -/
theorem crossingFace_weight
    (T : A1 ℂ) (α ν : ℂ) (q ρ s e : ℕ)
    (hν : ν ≠ 0) (hs : 0 < s) (hsρ : s < ρ) (he : 0 < e)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    vDeg ρ (-(s : ℤ)) T.1 = (e : ℤ) * ρ := by
  have hsupp := (crossingFace_starting_point T α ν q ρ s e
    hν hs hsρ he hface).1
  have hw := weight_of_mem_leadingForm T ρ (-(s : ℤ)) (expo e 0) hsupp
  rw [expo_weight] at hw
  simpa using hw.symm

/-- The displayed pure-power face has weight `eρ` for every `s`, including
the horizontal boundary `s=0`. Nonzero support and homogeneity suffice; no
strict-crossing starting-point lemma is used. -/
theorem crossingFace_weight_any_s
    (T : A1 ℂ) (α ν : ℂ) (q ρ s e : ℕ)
    (hν : ν ≠ 0) (hρ : 0 < ρ)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    vDeg ρ (-(s : ℤ)) T.1 = (e : ℤ) * ρ := by
  let R : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 *
    (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q
  have hR : R ≠ 0 := by
    simpa [R] using crossingBase_ne_zero α q ρ s hρ
  have hF : leadingForm ρ (-(s : ℤ)) T.1 ≠ 0 := by
    rw [hface]
    exact mul_ne_zero (by simpa using hν) (pow_ne_zero _ hR)
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hF
  have hhom : (leadingForm ρ (-(s : ℤ)) T.1).IsWeightedHomogeneous
      (wt ρ (-(s : ℤ))) ((e : ℤ) * ρ) := by
    rw [hface]
    have hRhom := crossingBase_isWeightedHomogeneous α q ρ s
    convert (hRhom.pow e).C_mul ν using 1 <;> simp
  have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
  have hv := weight_of_mem_leadingForm T ρ (-(s : ℤ)) d hd
  rw [hv] at hw
  exact hw

end Dixmier.Weyl
