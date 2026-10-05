/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalRootBudget

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Two finite roots exhaust the diagonal degree

Two distinct cut roots force degree two of the homogeneous companion.
The highest-coefficient identity then makes the cut degree equal to the
operator's diagonal weight, excluding a residual first-axis factor.
-/
namespace Dixmier.Weyl

/-- Two distinct roots leave no diagonal degree outside the scalar cut. -/
theorem preliminary_diagonal_two_roots_exhaust_weight
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hroots : 2 ≤ (cutPoly 1 1 P.1).roots.toFinset.card) :
    vDeg 1 1 P.1 = ((cutPoly 1 1 P.1).natDegree : ℤ) := by
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1 hdir
  obtain ⟨T,hTne,hweight,hdegree,hface⟩ := preliminary_companion_has_polynomial_cut_witness
    hsource 1 (by norm_num) P Q hpair 1 1 hdir (by norm_num) (by norm_num)
  have hPne : P ≠ 0 := by
    intro hz
    have hcomm := hpair.1
    rw [hz] at hcomm
    have hv := congrArg Subtype.val hcomm
    simp at hv
  have hLiftP : polynomialRamifiedLift 1 P ≠ 0 := by
    simpa [polynomialRamifiedLift_zero 1 (by norm_num)] using
      (polynomialRamifiedLift_injective 1 (by norm_num)).ne hPne
  have hLiftT : polynomialRamifiedLift 1 T ≠ 0 := by
    simpa [polynomialRamifiedLift_zero 1 (by norm_num)] using
      (polynomialRamifiedLift_injective 1 (by norm_num)).ne hTne
  have hPface := polynomialRamifiedLift_topFace_eq_cutPoly_of_pos 1 (by norm_num)
    P 1 1 (by norm_num) (by norm_num) hp
  have hbudget := ramified_source_companion_top_face_root_count 1 (by norm_num)
    1 1 (by norm_num) (by norm_num) (polynomialRamifiedLift 1 P)
    (polynomialRamifiedLift 1 T) hLiftP hLiftT hdegree hface hweight
  rw [hPface] at hbudget
  have hneg : polynomialRamifiedLift 1 (-T) = -polynomialRamifiedLift 1 T :=
    map_neg (polynomialRamifiedLiftHom 1 (by norm_num)) T
  have hnegweight : ramifiedWeightDeg 1 (by norm_num) 1 1
      (polynomialRamifiedLift 1 (-T)) = (2 : ℤ) := by
    rw [hneg,ramifiedWeightDeg_neg,hweight]
    norm_num
  have hbound := polynomialRamified_diagonal_topFace_natDegree_le (-T) 2 hnegweight
  rw [hneg] at hbound
  have htwo : (ramifiedTopFacePolynomial 1 (by norm_num) 1 1
      (-polynomialRamifiedLift 1 T)).natDegree = 2 := by omega
  have hcard : (cutPoly 1 1 P.1).roots.toFinset.card ≤ (cutPoly 1 1 P.1).natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hPdegree : 0 < (ramifiedTopFacePolynomial 1 (by norm_num) 1 1
      (polynomialRamifiedLift 1 P)).natDegree := by rw [hPface]; omega
  have hPweight : ramifiedWeightDeg 1 (by norm_num) 1 1 (polynomialRamifiedLift 1 P) =
      1 * vDeg 1 1 P.1 := by
    simpa using polynomialRamifiedLift_weightDeg_eq_of_pos 1 (by norm_num) P 1 1
      (by norm_num) (by norm_num) hp
  have hi := ramified_source_companion_endpoint_degree_identity 1 (by norm_num)
    1 1 (by norm_num) (by norm_num) (by norm_num)
    (polynomialRamifiedLift 1 P) (polynomialRamifiedLift 1 T) (vDeg 1 1 P.1)
    hLiftP hLiftT hPweight hdegree hface hweight hPdegree (by rw [htwo])
  rw [htwo,hPface] at hi
  norm_num [ramifiedCutExponent] at hi
  omega

end Dixmier.Weyl
