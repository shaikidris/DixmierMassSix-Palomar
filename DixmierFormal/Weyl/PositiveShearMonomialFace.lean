/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPositiveBinomialReconstruction
public import DixmierFormal.Weyl.PolynomialCutTranslation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Monomial face after the positive root shear

The actual positive binomial face and its polynomial root shear give a
new polynomial counterexample whose face is a single occupied monomial.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The cut of a weighted binomial face keeps its linear-factor power. -/
theorem positive_binomial_face_cut
    (P : A1 ℂ) (σ a k : ℕ) (lam α : ℂ)
    (hf : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^k) :
    cutPoly 1 (σ : ℤ) P.1 = C lam * (X-C α)^k := by
  rw [cutPoly,hf]
  let φ := MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then (1 : ℂ[X]) else Polynomial.X)
  change φ _ = _
  simp only [map_mul,map_pow,map_sub]
  dsimp [φ]
  simp only [MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
  norm_num

/-- The exact root shear recovers the weighted monomial in polynomial A₁. -/
theorem polynomial_root_shear_monomial_face
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a k : ℕ) (lam α : ℂ)
    (hd : vDeg 1 (σ : ℤ) P.1 = ((a+σ*k : ℕ) : ℤ))
    (hc : cutPoly 1 (σ : ℤ) P.1 = C lam * (X-C α)^k) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      polynomialRamifiedLift 1 R = ramifiedCutAut 1 (by norm_num) 1 (σ : ℤ) α
        (polynomialRamifiedLift 1 P) ∧
      leadingForm 1 (σ : ℤ) R.1 = MvPolynomial.C lam *
        MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ k := by
  obtain ⟨R,S,hRS,hR,hw,hcut⟩ := polynomial_monomial_cut_removes_root P Q hpair σ lam α k hc
  have hdegree : vDeg 1 (σ : ℤ) R.1 = ((a+σ*k : ℕ) : ℤ) := hw.trans hd
  have hf := positive_face_eq_of_linear_power_cut R lam 0 σ a k hdegree
    (by simpa using hcut)
  exact ⟨R,S,hRS,hR,by simpa using hf⟩

/-- Every actual nontrivial positive face can be sheared to a weighted
monomial without losing the polynomial counterexample relation. -/
theorem preliminary_positive_face_shear_monomial
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ : ℕ) (hσ : 1 < σ) (hfaceDir : InDir 1 (σ : ℤ) P.1) :
    ∃ (lam α : ℂ) (a k : ℕ) (R S : A1 ℂ),
      lam ≠ 0 ∧ α ≠ 0 ∧ 1 ≤ k ∧ IsCounterexamplePair R S ∧
      polynomialRamifiedLift 1 R = ramifiedCutAut 1 (by norm_num) 1 (σ : ℤ) α
        (polynomialRamifiedLift 1 P) ∧
      leadingForm 1 (σ : ℤ) R.1 = MvPolynomial.C lam *
        MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ k := by
  obtain ⟨lam,α,a,k,hlam,hα,hk,hd,hf⟩ :=
    preliminary_positive_face_binomial hsource P Q hpair σ hσ hfaceDir
  obtain ⟨R,S,hRS,hR,hmono⟩ := polynomial_root_shear_monomial_face P Q hpair σ a k lam α hd
    (positive_binomial_face_cut P σ a k lam α hf)
  exact ⟨lam,α,a,k,R,S,hlam,hα,hk,hRS,hR,hmono⟩

end Dixmier.Weyl
