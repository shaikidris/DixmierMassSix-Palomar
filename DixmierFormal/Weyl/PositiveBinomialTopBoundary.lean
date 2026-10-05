/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveBinomialMassBound

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Highest-Y boundary of a positive binomial face

The top binomial point bounds all Y-exponents and is the rightmost
occupied point in that row.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The highest cut coefficient identifies the binomial's top face point. -/
theorem positive_binomial_top_face_point
    (P : A1 ℂ) (σ a b : ℕ) (lam α : ℂ) (hlam : lam ≠ 0)
    (hd : vDeg 1 (σ : ℤ) P.1 = ((a+σ*b : ℕ) : ℤ))
    (hf : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^b) :
    expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support ∧
      ∀ d ∈ (leadingForm 1 (σ : ℤ) P.1).support, d 1 ≤ b := by
  classical
  have hc := positive_binomial_face_cut P σ a b lam α hf
  have hdeg : (cutPoly 1 (σ : ℤ) P.1).natDegree = b := by
    rw [hc,natDegree_C_mul hlam,natDegree_pow,natDegree_X_sub_C]; simp
  have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero b (X_sub_C_ne_zero α))
  have hn : (cutPoly 1 (σ : ℤ) P.1).coeff b ≠ 0 := by
    rw [← hdeg,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hne
  constructor
  · rw [MvPolynomial.mem_support_iff]
    rw [← cutPoly_coeff_at_face_point P 1 (σ : ℤ) a b (by norm_num)
      (by rw [hd]; push_cast; ring)]
    exact hn
  · intro d hdm
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
    have hw := (polynomialFace_point_source_data P 1 (σ : ℤ) i j hdm).2
    have hcoeff := cutPoly_coeff_at_face_point P 1 (σ : ℤ) i j (by norm_num)
      (by simpa using hw)
    have hnonzero : (cutPoly 1 (σ : ℤ) P.1).coeff j ≠ 0 := by
      rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hdm
    have hle := le_natDegree_of_ne_zero hnonzero
    simpa [expo,hdeg] using hle

/-- The native positive binomial top point is the rightmost point of the
highest occupied Y-row. -/
theorem preliminary_positive_binomial_top_boundary
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (lam α : ℂ) (hlam : lam ≠ 0)
    (hd : vDeg 1 (σ : ℤ) P.1 = ((a+σ*b : ℕ) : ℤ))
    (hf : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^b) :
    expo a b ∈ (symbol P.1).support ∧
      (∀ d ∈ (symbol P.1).support, d 1 ≤ b) ∧
      (∀ d ∈ (symbol P.1).support, d 1 = b → d 0 ≤ a) := by
  obtain ⟨hpoint,hlast⟩ := positive_binomial_top_face_point P σ a b lam α hlam hd hf
  refine ⟨(polynomialFace_point_source_data P 1 (σ : ℤ) a b hpoint).1,
    preliminary_positive_last_point_y_bound hsource P Q hpair σ a b hσ hpoint
      (by simpa [expo] using hlast) hb,?_⟩
  intro d hdm hj
  have hw := ((leadingForm_mem_iff_rational_slope P 1 (σ : ℤ)
    (by norm_num) (expo a b)).mp hpoint).2 d hdm
  simp [rationalNewtonWeight,expo,hj] at hw
  exact_mod_cast hw

/-- A negative-grade rightmost point of the highest row transfers its
sign to the positive binomial endpoint and hence gives the mass estimate. -/
theorem preliminary_positive_binomial_mass_of_negative_top_boundary
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 < σ) (hb : 0 < b)
    (lam α : ℂ) (hlam : lam ≠ 0) (hα : α ≠ 0)
    (hd : vDeg 1 (σ : ℤ) P.1 = ((a+σ*b : ℕ) : ℤ))
    (hf : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^b)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (symbol P.1).support)
    (hey : ∀ d ∈ (symbol P.1).support, d 1 ≤ e 1)
    (hex : ∀ d ∈ (symbol P.1).support, d 1 = e 1 → d 0 ≤ e 0)
    (hnegative : grade e < 0) : 10 ≤ mass P.1 := by
  obtain ⟨hpoint,hy,hx⟩ := preliminary_positive_binomial_top_boundary hsource P Q hpair
    σ a b (by omega) hb lam α hlam hd hf
  have heyLe := hy e he
  have hby := hey (expo a b) hpoint
  have hej : e 1 = b := by simp [expo] at hby; omega
  have hexLe := hx e he hej
  have hax := hex (expo a b) hpoint (by simpa [expo] using hej.symm)
  have hei : e 0 = a := by simp [expo] at hax; omega
  have hab : a < b := by
    dsimp [grade] at hnegative
    rw [hej,hei] at hnegative
    omega
  exact preliminary_positive_binomial_mass_ge_ten hsource hdegree P Q hpair σ a b hσ hab
    lam α hlam hα hd hf

end Dixmier.Weyl
