/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalFaceClassification
public import DixmierFormal.Weyl.GGVOriginalSubrectangularCases
public import DixmierFormal.Weyl.TwoRootTotalDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Original-pair alternatives for positive diagonal monomials

A finite zero root together with a positive residual axis exponent reconstructs
the positive monomial branch of the diagonal case map.
-/
namespace Dixmier.Weyl

/-- A diagonal monomial with two positive exponents satisfies the exact
original-or-Fourier case alternative. -/
theorem preliminary_diagonal_monomial_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (lam : ℂ) (a b : ℕ) (hlam : lam ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hface : leadingForm 1 1 P.1 = MvPolynomial.C lam *
      MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  classical
  have hm : leadingForm 1 1 P.1 = MvPolynomial.monomial (expo a b) lam := by
    rw [hface, MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.monomial_add_single]
    rfl
  have hs : (leadingForm 1 1 P.1).support = {expo a b} := by
    rw [hm, MvPolynomial.support_monomial]
    simp [hlam]
  have hmem : expo a b ∈ (leadingForm 1 1 P.1).support := by simp [hs]
  have hw := (polynomialFace_point_source_data P 1 1 a b hmem).2
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
    (by norm_num [IsDirection])
  have ht := totalDeg_eq_vDeg_one_one P hp
  have hd : totalDeg P.1 = a + b := by
    norm_num at hw
    omega
  exact preliminary_positive_singleton_diagonal_caseSplit hsource P Q hpair a b hd
    hmem (by intro d hd; simpa [hs] using hd) ha hb

/-- A pure power cut with a positive residual first-axis exponent belongs
to the positive diagonal monomial branch. -/
theorem preliminary_zero_root_cut_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (lam : ℂ) (a k : ℕ) (hlam : lam ≠ 0) (ha : 0 < a) (hk : 0 < k)
    (hdegree : vDeg 1 1 P.1 = ((a+k : ℕ) : ℤ))
    (hcut : cutPoly 1 1 P.1 = Polynomial.C lam * Polynomial.X ^ k) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  have hf := diagonal_face_eq_of_factored_cut P lam 0 0 a k 0
    (by simpa using hdegree) (by simpa using hcut)
  apply preliminary_diagonal_monomial_caseSplit hsource P Q hpair lam a k hlam ha hk
  simpa using hf

end Dixmier.Weyl
