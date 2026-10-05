/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingFaceEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Starting endpoint of a pure-power crossing face

The lowest `x`-degree supplies an actual support monomial at `(e,0)`.
Weighted homogeneity shows that its grade is maximal on the face.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- The explicit face starts at `(e,0)`, which has maximal grade on it. -/
theorem crossingFace_starting_endpoint
    (α ν : ℂ) (q ρ s e : ℕ)
    (hν : ν ≠ 0) (hs : 0 < s) (hsρ : s < ρ) (he : 0 < e)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    expo e 0 ∈ F.support ∧
      (∀ d ∈ F.support, grade d ≤ grade (expo e 0)) := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let R : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 * (1 + MvPolynomial.C α *
      MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q
  have hRtrail : (E (R ^ e)).natTrailingDegree = e := by
    simpa [E, R] using crossingBase_power_natTrailingDegree α q ρ s e hs
  have hRne : E (R ^ e) ≠ 0 := by
    intro hz
    simp [hz] at hRtrail
    omega
  have hνC : (MvPolynomial.C ν : MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    simpa using hν
  have hmap : E F = Polynomial.C (MvPolynomial.C ν) * E (R ^ e) := by
    rw [hF]
    simp [E, R, MvPolynomial.finSuccEquiv_apply]
  have hEne : E F ≠ 0 := by
    rw [hmap]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hνC) hRne
  have hEtrail : (E F).natTrailingDegree = e := by
    rw [hmap, Polynomial.natTrailingDegree_mul
      (Polynomial.C_ne_zero.mpr hνC) hRne,
      Polynomial.natTrailingDegree_C, hRtrail]
    omega
  have hbottom : e ∈ (E F).support := by
    rw [← hEtrail]
    exact Polynomial.natTrailingDegree_mem_support_of_nonzero hEne
  rw [MvPolynomial.support_finSuccEquiv] at hbottom
  obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp hbottom
  have hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((e : ℤ) * ρ) := by
    rw [hF]
    have hRhom := crossingBase_isWeightedHomogeneous α q ρ s
    convert (hRhom.pow e).C_mul ν using 1 <;> simp
  have hdweight := hhom (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hi : i = e := by simpa [expo] using hd0
  rw [expo_weight] at hdweight
  have hj : j = 0 := by
    rw [hi] at hdweight
    have hsne : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hmul : (s : ℤ) * (j : ℤ) = 0 := by nlinarith [hdweight]
    have hjz : (j : ℤ) = 0 := (mul_eq_zero.mp hmul).resolve_left hsne
    exact_mod_cast hjz
  subst i
  subst j
  constructor
  · simpa only [expo] using hd
  · intro d hd
    obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
    have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
    rw [expo_weight] at hw
    have hρz : 0 < (ρ : ℤ) := by exact_mod_cast (Nat.zero_lt_of_lt hsρ)
    have hgap : 0 ≤ (ρ : ℤ) - s := by omega
    have hnonneg : 0 ≤ ((ρ : ℤ) - s) * (j : ℤ) :=
      mul_nonneg hgap (by exact_mod_cast Nat.zero_le j)
    simp [grade, expo]
    nlinarith [hw, hnonneg]

/-- The starting-point premise for a maximum-root cut, for an operator with
the specified explicit leading face. -/
theorem crossingFace_starting_point
    (T : A1 ℂ) (α ν : ℂ) (q ρ s e : ℕ)
    (hν : ν ≠ 0) (hs : 0 < s) (hsρ : s < ρ) (he : 0 < e)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    expo e 0 ∈ (leadingForm ρ (-(s : ℤ)) T.1).support ∧
      (∀ d ∈ (leadingForm ρ (-(s : ℤ)) T.1).support,
        grade d ≤ grade (expo e 0)) := by
  exact crossingFace_starting_endpoint α ν q ρ s e hν hs hsρ he _ hface
end Dixmier.Weyl
