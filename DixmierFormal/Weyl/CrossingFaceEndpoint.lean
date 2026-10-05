/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingFaceSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Ending endpoint of a pure-power crossing face

The highest `x`-degree in the explicit face determines an actual support
monomial. Weighted homogeneity fixes its `y`-degree, and the paper's parameter
identity makes its grade exactly `-eρ`.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- The explicit face has an ending support monomial at
`(e+s(qe), ρqe)` whose grade is exactly `-eρ`. -/
theorem crossingFace_ending_endpoint
    (α ν : ℂ) (q ρ s e : ℕ)
    (hα : α ≠ 0) (hν : ν ≠ 0)
    (hq : 2 ≤ q) (hs : 0 < s) (he : 0 < e)
    (hparam : (q - 1) * ρ = q * s + 1)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    expo (e + s * (q * e)) (ρ * q * e) ∈ F.support ∧
      grade (expo (e + s * (q * e)) (ρ * q * e)) =
        -((e : ℤ) * ρ) := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let R : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 * (1 + MvPolynomial.C α *
      MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q
  have hRdeg : (E (R ^ e)).natDegree = e + s * (q * e) := by
    simpa [E, R] using crossingBase_power_natDegree α q ρ s e hα hs
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
  have hEdeg : (E F).natDegree = e + s * (q * e) := by
    rw [hmap, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hνC) hRne,
      Polynomial.natDegree_C, hRdeg]
    omega
  have htop : e + s * (q * e) ∈ (E F).support := by
    rw [← hEdeg]
    exact Polynomial.natDegree_mem_support_of_nonzero hEne
  rw [MvPolynomial.support_finSuccEquiv] at htop
  obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp htop
  have hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((e : ℤ) * ρ) := by
    rw [hF]
    have hRhom := crossingBase_isWeightedHomogeneous α q ρ s
    convert (hRhom.pow e).C_mul ν using 1 <;> simp
  have hdweight := hhom (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hi : i = e + s * (q * e) := by simpa [expo] using hd0
  rw [expo_weight] at hdweight
  have hj : j = ρ * q * e := by
    have hsne : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hmul : (s : ℤ) * ((j : ℤ) - ((ρ * q * e : ℕ) : ℤ)) = 0 := by
      rw [hi] at hdweight
      push_cast at hdweight ⊢
      nlinarith [hdweight]
    have hdiff : (j : ℤ) = ((ρ * q * e : ℕ) : ℤ) := by
      have hz := (mul_eq_zero.mp hmul).resolve_left hsne
      omega
    exact_mod_cast hdiff
  subst i
  subst j
  constructor
  · simpa only [expo] using hd
  · have hidentity := purePower_weight_identity hq hparam
    simp [grade, expo]
    nlinarith [hidentity]

/-- An operator with this face has the negative ending grade required by the
GGV maximum-root cut. -/
theorem crossingFace_ending_grade_negative
    (T : A1 ℂ) (α ν : ℂ) (q ρ s e : ℕ)
    (hα : α ≠ 0) (hν : ν ≠ 0)
    (hq : 2 ≤ q) (hs : 0 < s) (he : 0 < e)
    (hparam : (q - 1) * ρ = q * s + 1)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    ∃ d ∈ (leadingForm ρ (-(s : ℤ)) T.1).support, grade d < 0 := by
  obtain ⟨hsupp, hgrade⟩ := crossingFace_ending_endpoint α ν q ρ s e
    hα hν hq hs he hparam _ hface
  refine ⟨expo (e + s * (q * e)) (ρ * q * e), hsupp, ?_⟩
  rw [hgrade]
  have hρ := purePower_rho_pos hq hparam
  have hprod : 0 < (e : ℤ) * ρ := by
    exact mul_pos (by exact_mod_cast he) (by exact_mod_cast hρ)
  omega

/-- Both members of the exact terminal pair have negative ending grades in
the shared pure-power direction. -/
theorem crossingPair_ending_grades_negative
    (P Q : A1 ℂ) (α μ ν : ℂ) (p q j ρ s : ℕ)
    (hα : α ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hp : 0 < p) (hq : 2 ≤ q) (hj : 0 < j) (hs : 0 < s)
    (hparam : (q - 1) * ρ = q * s + 1)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ j) :
    (∃ d ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, grade d < 0) ∧
    (∃ d ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support, grade d < 0) := by
  exact ⟨crossingFace_ending_grade_negative P α μ q ρ s p
      hα hμ hq hs hp hparam hPface,
    crossingFace_ending_grade_negative Q α ν q ρ s j
      hα hν hq hs hj hparam hQface⟩
end Dixmier.Weyl
