/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveShearFiniteDescent
public import DixmierFormal.Weyl.FaceCutMass
public import DixmierFormal.Scalar.SparseRoots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Mass bound from a positive binomial face

Finite polynomial descent supplies the degree of a terminal pair. A
separate uniform degree bound then bounds the original face multiplicity.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The positive-face mass estimate keeps the uniform degree input explicit. -/
theorem preliminary_positive_binomial_mass_ge_ten
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 < σ) (hab : a < b)
    (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hd : vDeg 1 (σ : ℤ) P.1 = ((a+σ*b : ℕ) : ℤ))
    (hf : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^b) :
    10 ≤ mass P.1 := by
  classical
  have hc := positive_binomial_face_cut P σ a b lam α hf
  obtain ⟨R,S,hRS,hR,hmono⟩ := polynomial_root_shear_monomial_face P Q hpair σ a b lam α hd hc
  have hs : (leadingForm 1 (σ : ℤ) R.1).support = {expo a b} := by
    rw [hmono]; exact weighted_monomial_support lam hlam a b
  obtain ⟨T,U,hTU,htotal⟩ := preliminary_positive_singleton_finite_descent hsource R S hRS
    σ a b (by omega) (by omega) (by rw [hs]; simp)
    (by intro d hdm; simpa [hs] using hdm)
  have hsum : 16 ≤ a+b := by rw [← htotal]; exact hdegree T U hTU
  have hb : 9 ≤ b := by omega
  have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero b (X_sub_C_ne_zero α))
  have hdiv : (X-C α)^b ∣ cutPoly 1 (σ : ℤ) P.1 := by
    rw [hc]; exact dvd_mul_left _ _
  have hterms := Dixmier.pow_dvd_imp_lt_termCount hne hα hdiv
  have hmass := cutPoly_termCount_le_mass P 1 (σ : ℤ) (by omega)
  omega

end Dixmier.Weyl
