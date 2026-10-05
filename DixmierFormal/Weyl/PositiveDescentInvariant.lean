module

public import DixmierFormal.Weyl.PositiveShearMonomialFace
public import DixmierFormal.Weyl.GGVPositiveCompanionEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Invariant top point of the positive-face descent

A shared highest-Y point determines both exponents of the next binomial.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The next positive binomial has exactly the retained top-point exponents. -/
theorem preliminary_positive_binomial_at_top_point
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 < σ)
    (hface : InDir 1 (σ : ℤ) P.1)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hy : ∀ d ∈ (symbol P.1).support, d 1 ≤ b) :
    ∃ lam α : ℂ, lam ≠ 0 ∧ α ≠ 0 ∧
      vDeg 1 (σ : ℤ) P.1 = ((a+σ*b : ℕ) : ℤ) ∧
      leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
        (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^b := by
  classical
  obtain ⟨lam,α,a',k,hlam,hα,hk,hd,hf⟩ :=
    preliminary_positive_face_binomial hsource P Q hpair σ hσ hface
  have hc := positive_binomial_face_cut P σ a' k lam α hf
  have hdeg : (cutPoly 1 (σ : ℤ) P.1).natDegree = k := by
    rw [hc,natDegree_C_mul hlam,natDegree_pow,natDegree_X_sub_C]
    simp
  have hw := (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).2
  have hcoeff := cutPoly_coeff_at_face_point P 1 (σ : ℤ) a b (by norm_num)
    (by simpa using hw)
  have hbn : (cutPoly 1 (σ : ℤ) P.1).coeff b ≠ 0 := by
    rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hmem
  have hbk : b ≤ k := by simpa [hdeg] using le_natDegree_of_ne_zero hbn
  have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
    intro hz; rw [hz] at hbn; exact hbn (by simp)
  have hs := cutPolynomial_support_subset_y_exponents
    (leadingForm 1 (σ : ℤ) P.1) (natDegree_mem_support_of_nonzero hne)
  obtain ⟨d,hdmem,he⟩ := Finset.mem_image.mp hs
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
  have hj : j = k := by
    have hdegEval := hdeg
    unfold cutPoly at hdegEval
    simpa [expo] using he.trans hdegEval
  have hsourcePoint := (polynomialFace_point_source_data P 1 (σ : ℤ) i j hdmem).1
  have hkb : k ≤ b := by simpa [expo,hj] using hy (expo i j) hsourcePoint
  have hkeq : k = b := by omega
  rw [hkeq] at hd hf
  have haeq : a' = a := by norm_num at hw hd; nlinarith [hw,hd]
  subst a'
  exact ⟨lam,α,hlam,hα,hd,hf⟩

end Dixmier.Weyl
