/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift
public import DixmierFormal.Weyl.RamifiedCompanionRootBudget

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The diagonal companion root budget

A polynomial companion of diagonal weight two has top cut degree at most
two. The exact source leading bracket therefore bounds the distinct roots
of the diagonal cut polynomial, without a mass or degree cutoff.
-/
namespace Dixmier.Weyl

/-- Nonnegative polynomial PBW exponents bound the degree of the
canonical diagonal top-face polynomial by its weight. -/
theorem polynomialRamified_diagonal_topFace_natDegree_le
    (T : A1 ℂ) (n : ℕ)
    (hweight : ramifiedWeightDeg 1 (by norm_num) 1 1 (polynomialRamifiedLift 1 T) = (n : ℤ)) :
    (ramifiedTopFacePolynomial 1 (by norm_num) 1 1 (polynomialRamifiedLift 1 T)).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hne
  have hs := Polynomial.mem_support_iff.mpr hne
  obtain ⟨hmem, htop⟩ :=
    (ramifiedTopFacePolynomial_mem_support_iff 1 (by norm_num) 1 1
      (polynomialRamifiedLift 1 T) j).mp hs
  have hk := ramifiedPBWTopLaurent_mem 1 (by norm_num) (polynomialRamifiedLift 1 T) j hmem
  have hsupport : (ramifiedPBWTopLaurent 1 (by norm_num) (polynomialRamifiedLift 1 T) j, j) ∈
      ramifiedPBWSupport 1 (by norm_num) (polynomialRamifiedLift 1 T) :=
    (ramifiedPBWSupport_mem_iff 1 (by norm_num) _ _ j).mpr
      (by simpa only [ramifiedPBWCoeff] using Finsupp.mem_support_iff.mp hk)
  obtain ⟨i, hi, _⟩ :=
    (polynomialRamifiedLift_support_iff_scaled 1 (by norm_num) T _ j).mp hsupport
  have hsum : (i : ℤ) + j = n := by simpa [hweight, hi] using htop
  omega

/-- The preliminary diagonal companion gives at most two distinct
roots of the actual diagonal cut polynomial. -/
theorem preliminary_diagonal_cut_distinct_roots_le_two
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    (cutPoly 1 1 P.1).roots.toFinset.card ≤ 2 := by
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  obtain ⟨T, hTne, hweight, hdegree, hface⟩ :=
    preliminary_companion_has_polynomial_cut_witness hsource 1 (by norm_num)
      P Q hpair 1 1 hdir (by norm_num) (by norm_num)
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
    1 (by norm_num) 1 1 (by norm_num) (by norm_num)
      (polynomialRamifiedLift 1 P) (polynomialRamifiedLift 1 T)
      hLiftP hLiftT hdegree hface hweight
  have hneg : polynomialRamifiedLift 1 (-T) = -polynomialRamifiedLift 1 T :=
    map_neg (polynomialRamifiedLiftHom 1 (by norm_num)) T
  have hnegweight : ramifiedWeightDeg 1 (by norm_num) 1 1
      (polynomialRamifiedLift 1 (-T)) = (2 : ℤ) := by
    rw [hneg, ramifiedWeightDeg_neg, hweight]
    norm_num
  have hbound := polynomialRamified_diagonal_topFace_natDegree_le (-T) 2 hnegweight
  rw [← hneg] at hbudget
  rw [polynomialRamifiedLift_topFace_eq_cutPoly_of_pos 1 (by norm_num)
    P 1 1 (by norm_num) (by norm_num)
      (counterexample_vDeg_pos_all_directions P Q hpair 1 1 hdir)] at hbudget
  exact hbudget.trans hbound

end Dixmier.Weyl
