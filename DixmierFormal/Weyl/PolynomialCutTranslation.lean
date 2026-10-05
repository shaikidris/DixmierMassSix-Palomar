/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialMonomialShearRecovery
public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift
public import DixmierFormal.Weyl.RamifiedShearTopFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exact polynomial cut translation

The faithful lift transfers the full ramified top-face formula to the
polynomial Weyl algebra, including its weight and entire cut polynomial.
-/
namespace Dixmier.Weyl
open Polynomial

/-- Polynomial recovery transports both weight and the entire cut polynomial. -/
theorem polynomial_monomial_cut_weight_and_translate
    (P R : A1 ℂ) (σ : ℕ) (c : ℂ) (hPne : P ≠ 0)
    (hp : 0 < vDeg 1 (σ : ℤ) P.1) (hr : 0 < vDeg 1 (σ : ℤ) R.1)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 (σ : ℤ) c (polynomialRamifiedLift 1 P)) :
    vDeg 1 (σ : ℤ) R.1 = vDeg 1 (σ : ℤ) P.1 ∧
      cutPoly 1 (σ : ℤ) R.1 = (cutPoly 1 (σ : ℤ) P.1).comp (X+C c) := by
  have hLift : polynomialRamifiedLift 1 P ≠ 0 := by
    simpa [polynomialRamifiedLift_zero 1 (by norm_num)] using
      (polynomialRamifiedLift_injective 1 (by norm_num)).ne hPne
  have hw := polynomialRamifiedLift_weightDeg_eq_of_pos 1 (by norm_num) P
    1 (σ : ℤ) (by norm_num) (by norm_num) hp
  have hs := ramifiedCutAut_topFace_eq_translate_of_weight
    1 (by norm_num) 1 (σ : ℤ) (vDeg 1 (σ : ℤ) P.1)
    (by norm_num) (by norm_num) (by positivity) c
    (polynomialRamifiedLift 1 P) hLift (by simpa using hw)
  rw [← hrecover] at hs
  have hwR := polynomialRamifiedLift_weightDeg_eq_of_pos 1 (by norm_num) R
    1 (σ : ℤ) (by norm_num) (by norm_num) hr
  constructor
  · simpa [hwR] using hs.1
  · rw [polynomialRamifiedLift_topFace_eq_cutPoly_of_pos 1 (by norm_num)
      R 1 (σ : ℤ) (by norm_num) (by norm_num) hr,
      polynomialRamifiedLift_topFace_eq_cutPoly_of_pos 1 (by norm_num)
      P 1 (σ : ℤ) (by norm_num) (by norm_num) hp] at hs
    exact hs.2

/-- The exact polynomial shear at a cut root removes that root while
preserving the counterexample pair and its cut weight. -/
theorem polynomial_monomial_cut_removes_root
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ : ℕ) (lam α : ℂ) (k : ℕ)
    (hcut : cutPoly 1 (σ : ℤ) P.1 = C lam * (X-C α)^k) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      polynomialRamifiedLift 1 R = ramifiedCutAut 1 (by norm_num) 1 (σ : ℤ) α
        (polynomialRamifiedLift 1 P) ∧
      vDeg 1 (σ : ℤ) R.1 = vDeg 1 (σ : ℤ) P.1 ∧
      cutPoly 1 (σ : ℤ) R.1 = C lam * X^k := by
  obtain ⟨R,S,hRS,hR,hS⟩ :=
    polynomial_monomial_cut_recovers_polynomial_counterexample σ α P Q hpair
  have hdir : IsDirection 1 (σ : ℤ) := ⟨by simp, by positivity⟩
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 (σ : ℤ) hdir
  have hr := counterexample_vDeg_pos_all_directions R S hRS 1 (σ : ℤ) hdir
  have hPne : P ≠ 0 := by
    intro hz
    have h := congrArg Subtype.val hpair.1
    rw [hz] at h
    simp at h
  have ht := polynomial_monomial_cut_weight_and_translate P R σ α hPne hp hr hR
  refine ⟨R,S,hRS,hR,ht.1,?_⟩
  rw [ht.2,hcut]
  simp only [mul_comp, pow_comp, sub_comp, X_comp, C_comp]
  simp

end Dixmier.Weyl
