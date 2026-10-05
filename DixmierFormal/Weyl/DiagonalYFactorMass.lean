/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DiagonalPureBinomialMass

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Positive-endpoint one-root diagonal mass alternative

For a residual Y-axis factor smaller than the nonzero root multiplicity,
the degree lower bound forces at least ten occupied grades.
-/
namespace Dixmier.Weyl
open Polynomial

/-- Retaining the residual axis exponent gives the precise operator degree. -/
theorem diagonal_y_factor_totalDeg
    (P : A1 ℂ) (b k : ℕ) (hk : 1 ≤ k)
    (lam α : ℂ) (hlam : lam ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    totalDeg P.1 = b+k := by
  have hshape : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C (0 : ℂ) * MvPolynomial.X 0)^b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k := by simpa using hf
  have hw := twoRoot_vDeg_eq_exponent_sum P lam 0 α b k hlam hshape
  have hp : 0 < vDeg 1 1 P.1 := by rw [hw]; omega
  have hd := totalDeg_eq_vDeg_one_one P hp
  omega

/-- The positive endpoint branch has mass at least ten. -/
theorem diagonal_y_factor_mass_ge_ten
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (b k : ℕ) (hbk : b < k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    10 ≤ mass P.1 := by
  have hk : 1 ≤ k := by omega
  have hd := diagonal_y_factor_totalDeg P b k hk lam α hlam hf
  have hlarge : 16 ≤ b+k := by rw [← hd]; exact hdegree P Q hpair
  have hshape : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C (0 : ℂ) * MvPolynomial.X 0)^b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k := by simpa using hf
  have hc := twoRoot_cutPoly P lam 0 α b k hshape
  simp only [map_zero, sub_zero] at hc
  have hne : cutPoly 1 1 P.1 ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero b X_ne_zero))
      (pow_ne_zero k (X_sub_C_ne_zero α))
  have hdiv : (X-C α)^k ∣ cutPoly 1 1 P.1 := by rw [hc]; exact dvd_mul_left _ _
  have ht := Dixmier.pow_dvd_imp_lt_termCount hne hα hdiv
  have hm := cutPoly_termCount_le_mass P 1 1 (by norm_num)
  omega

/-- The positive endpoint branch supplies the frozen case alternative. -/
theorem diagonal_y_factor_caseAlternative
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (b k : ℕ) (hbk : b < k) (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) :
    CaseAlternative P :=
  Or.inr (Or.inl (diagonal_y_factor_mass_ge_ten hdegree P Q hpair b k hbk lam α hlam hα hf))

end Dixmier.Weyl
