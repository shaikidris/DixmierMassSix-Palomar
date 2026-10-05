/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalRootBudget

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # One-root budget on positive-slope faces

A polynomial companion of weight 1+sigma with sigma>1 has cut degree at
most one. Root containment therefore restricts the actual positive cut.
-/
namespace Dixmier.Weyl

/-- Nonnegative polynomial exponents make the positive companion cut linear. -/
theorem polynomialRamified_positive_companion_cut_natDegree_le_one
    (T : A1 ℂ) (σ : ℕ) (hσ : 1 < σ)
    (hweight : ramifiedWeightDeg 1 (by norm_num) 1 (σ : ℤ)
      (polynomialRamifiedLift 1 T) = 1 + (σ : ℤ)) :
    (ramifiedTopFacePolynomial 1 (by norm_num) 1 (σ : ℤ)
      (polynomialRamifiedLift 1 T)).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hne
  have hs := Polynomial.mem_support_iff.mpr hne
  obtain ⟨hmem, htop⟩ :=
    (ramifiedTopFacePolynomial_mem_support_iff 1 (by norm_num) 1 (σ : ℤ)
      (polynomialRamifiedLift 1 T) j).mp hs
  have hk := ramifiedPBWTopLaurent_mem 1 (by norm_num) (polynomialRamifiedLift 1 T) j hmem
  have hsupport : (ramifiedPBWTopLaurent 1 (by norm_num) (polynomialRamifiedLift 1 T) j, j) ∈
      ramifiedPBWSupport 1 (by norm_num) (polynomialRamifiedLift 1 T) :=
    (ramifiedPBWSupport_mem_iff 1 (by norm_num) _ _ j).mpr
      (by simpa only [ramifiedPBWCoeff] using Finsupp.mem_support_iff.mp hk)
  obtain ⟨i, hi, _⟩ :=
    (polynomialRamifiedLift_support_iff_scaled 1 (by norm_num) T _ j).mp hsupport
  have heq : (i : ℤ) + (σ : ℤ) * (j : ℤ) = 1 + σ := by
    simpa [hweight, hi, mul_comm] using htop
  have hsZ : (1 : ℤ) < σ := by exact_mod_cast hσ
  have hjZ : (1 : ℤ) < j := by exact_mod_cast hj
  nlinarith

/-- The preliminary companion gives at most one distinct root of the
actual positive-slope cut, with no bound on operator degree or mate. -/
theorem preliminary_positive_cut_distinct_roots_le_one
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ : ℕ) (hσ : 1 < σ) :
    (cutPoly 1 (σ : ℤ) P.1).roots.toFinset.card ≤ 1 := by
  have hdir : IsDirection 1 (σ : ℤ) := by
    constructor
    · simp
    · positivity
  obtain ⟨T, hTne, hweight, hdegree, hface⟩ :=
    preliminary_companion_has_polynomial_cut_witness hsource 1 (by norm_num)
      P Q hpair 1 (σ : ℤ) hdir (by norm_num) (by norm_num)
  have hPne : P ≠ 0 := by
    intro hz
    have hcomm := hpair.1
    rw [hz] at hcomm
    have hcommOp := congrArg Subtype.val hcomm
    simp at hcommOp
  have hLiftP : polynomialRamifiedLift 1 P ≠ 0 := by
    simpa [polynomialRamifiedLift_zero 1 (by norm_num)] using
      (polynomialRamifiedLift_injective 1 (by norm_num)).ne hPne
  have hLiftT : polynomialRamifiedLift 1 T ≠ 0 := by
    simpa [polynomialRamifiedLift_zero 1 (by norm_num)] using
      (polynomialRamifiedLift_injective 1 (by norm_num)).ne hTne
  have hbudget := ramified_source_companion_top_face_root_count
    1 (by norm_num) 1 (σ : ℤ) (by norm_num) (by positivity)
      (polynomialRamifiedLift 1 P) (polynomialRamifiedLift 1 T)
      hLiftP hLiftT hdegree hface hweight
  have hneg : polynomialRamifiedLift 1 (-T) = -polynomialRamifiedLift 1 T :=
    map_neg (polynomialRamifiedLiftHom 1 (by norm_num)) T
  have hnegweight : ramifiedWeightDeg 1 (by norm_num) 1 (σ : ℤ)
      (polynomialRamifiedLift 1 (-T)) = 1 + (σ : ℤ) := by
    rw [hneg, ramifiedWeightDeg_neg, hweight]
    simp
  have hbound := polynomialRamified_positive_companion_cut_natDegree_le_one
    (-T) σ hσ hnegweight
  rw [← hneg] at hbudget
  rw [polynomialRamifiedLift_topFace_eq_cutPoly_of_pos 1 (by norm_num)
    P 1 (σ : ℤ) (by norm_num) (by norm_num)
      (counterexample_vDeg_pos_all_directions P Q hpair 1 (σ : ℤ) hdir)] at hbudget
  exact hbudget.trans hbound

end Dixmier.Weyl
