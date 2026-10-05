/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.TwoRootTotalDegree
public import DixmierFormal.Weyl.PositiveBinomialMassBound

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Mass bound for a diagonal binomial joining the axes

The diagonal exponent is the operator's total degree. A uniform degree
lower bound and the nonzero repeated root give seventeen occupied grades.
-/
namespace Dixmier.Weyl
open Polynomial

/-- A nonzero diagonal binomial obeys the mass-seventeen alternative. -/
theorem diagonal_pure_binomial_mass_ge_seventeen
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (k : ℕ) (hk : 1 ≤ k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    17 ≤ mass P.1 := by
  have hw : vDeg 1 1 P.1 = (k : ℤ) := by
    simpa using twoRoot_vDeg_eq_exponent_sum P lam α 0 k 0 hlam (by simpa using hf)
  have hp : 0 < vDeg 1 1 P.1 := by rw [hw]; omega
  have hd := totalDeg_eq_vDeg_one_one P hp
  have htotal : totalDeg P.1 = k := by omega
  have hlarge : 16 ≤ k := by rw [← htotal]; exact hdegree P Q hpair
  have hc := positive_binomial_face_cut P 1 0 k lam α (by simpa using hf)
  norm_num at hc
  have hne : cutPoly 1 1 P.1 ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero k (X_sub_C_ne_zero α))
  have hdiv : (X-C α)^k ∣ cutPoly 1 1 P.1 := by
    rw [hc]; exact dvd_mul_left _ _
  have hterms := Dixmier.pow_dvd_imp_lt_termCount hne hα hdiv
  have hmass := cutPoly_termCount_le_mass P 1 1 (by norm_num)
  omega

/-- The mass estimate supplies the frozen case-map alternative. -/
theorem diagonal_pure_binomial_caseAlternative
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (k : ℕ) (hk : 1 ≤ k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    CaseAlternative P := by
  have hm := diagonal_pure_binomial_mass_ge_seventeen hdegree P Q hpair k hk lam α hlam hα hf
  exact Or.inr (Or.inl (by omega))

end Dixmier.Weyl
