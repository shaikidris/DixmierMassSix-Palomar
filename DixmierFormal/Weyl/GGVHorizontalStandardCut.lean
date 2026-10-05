/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift
public import DixmierFormal.Weyl.GGVStandardNoHorizontalCut
public import DixmierFormal.Weyl.CornerRootOrderRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!+# The horizontal maximum-root cut of an oriented rectangle

The actual occupied corner determines the horizontal weight and cut degree.
Under the preliminary companion input, the largest root order exceeds the
corner's first coordinate. The exact maximum-root shear consequently makes
every occupied point of the old horizontal face negative-grade, while
preserving the commutator of the unrestricted mate. Polynomial recovery and
standard minimality are separate conclusions.
-/

namespace Dixmier.Weyl

/-- The occupied subrectangular corner computes both horizontal invariants. -/
theorem subrectangular_horizontal_weight_and_cut_degree
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b) :
    vDeg 1 0 P.1 = (a : ℤ) ∧ (cutPoly 1 0 P.1).natDegree = b := by
  have hend := subrectangular_corner_mem_horizontal P a b hrect
  have hw := (polynomialFace_point_source_data P 1 0 a b hend).2
  have hweight : vDeg 1 0 P.1 = (a : ℤ) := by simpa using hw.symm
  refine ⟨hweight, cutPoly_natDegree_of_min_grade_endpoint P 1 0 a b
    (by norm_num) (by norm_num) hend ?_⟩
  intro e he
  have hs := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) e).mp he
  have hexpo : expo (e 0) (e 1) = e := by
    ext i
    fin_cases i <;> simp [expo]
  have hwe := (polynomialFace_point_source_data P 1 0 (e 0) (e 1)
    (hexpo.symm ▸ he)).2
  have hx : e 0 = a := by
    rw [hweight] at hwe
    norm_num at hwe
    exact_mod_cast hwe
  have hy := (hrect.2 e hs.1).2
  simp [grade, expo, hx]
  omega

/-- At a genuine horizontal edge below grade zero, the source companion
forces a maximum root order strictly beyond the corner's first coordinate. -/
theorem preliminary_horizontal_maxRoot_above_corner
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b)
    (hab : a < b) (hface : InDir 1 0 P.1) :
    a < maxRootMult (cutPoly 1 0 P.1) := by
  obtain ⟨hweight, hdegree⟩ := subrectangular_horizontal_weight_and_cut_degree P a b hrect
  have hcutPos : 0 < (cutPoly 1 0 P.1).natDegree := by rw [hdegree]; omega
  have hOldEnd : ((1 : ℤ) / 1) * vDeg 1 0 P.1 -
      (ramifiedCutExponent 1 1 0 + (1 : ℤ)) *
        ((cutPoly 1 0 P.1).natDegree : ℤ) < 0 := by
    simpa [hweight, hdegree, ramifiedCutExponent] using
      (show (a : ℤ) - b < 0 by omega)
  have hneg := preliminary_companion_maxRoot_cut_grade_negative
    hsource 1 (by norm_num) P Q hpair 1 0 (by norm_num [IsDirection])
      (by norm_num) (by norm_num) hface hcutPos hOldEnd
  have hlt : (a : ℤ) < maxRootMult (cutPoly 1 0 P.1) := by
    simpa [ramifiedCutExponent, hweight, sub_neg] using hneg
  exact_mod_cast hlt

/-- The same selected root supplies the actual negative old-face start
and preserves the exact Weyl relation with no restriction on the mate. -/
theorem preliminary_horizontal_cut_negative_old_face_exact_pair
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b)
    (hab : a < b) (hface : InDir 1 0 P.1) :
    let M := maxRootMult (cutPoly 1 0 P.1)
    ∃ c : ℂ, (cutPoly 1 0 P.1).IsRoot c ∧
      (cutPoly 1 0 P.1).rootMultiplicity c = M ∧
      ((a : ℤ), M) ∈ ramifiedPBWSupport 1 (by norm_num)
        (ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P)) ∧
      (∀ u : ℤ, ∀ n : ℕ,
        (u,n) ∈ ramifiedPBWSupport 1 (by norm_num)
          (ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P)) →
        ramifiedWeight 1 1 0 (u,n) = (a : ℤ) → M ≤ n ∧ u - (n : ℤ) < 0) ∧
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 Q) *
          ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) -
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) *
          ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 Q) = 1 := by
  dsimp only
  have hlt := preliminary_horizontal_maxRoot_above_corner hsource P Q hpair a b hrect hab hface
  have hweight := (subrectangular_horizontal_weight_and_cut_degree P a b hrect).1
  obtain ⟨c, hc, hm, hp, hext, hcomm⟩ :=
    polynomialRamifiedCut_exact_pair_maxRoot_extremal 1 (by norm_num) P Q
      1 0 (by norm_num) (by norm_num) (by norm_num) hface hpair.1
  refine ⟨c, hc, hm, ?_, ?_, hcomm⟩
  · simpa [ramifiedCutExponent, hweight] using hp
  · intro u n hun hwn
    have hwn' : ramifiedWeight 1 1 0 (u,n) =
        1 * (((1 : ℤ) / 1) * vDeg 1 0 P.1) := by simpa [hweight] using hwn
    obtain ⟨hmin, hgrade⟩ := hext u n hun hwn'
    have hbound : u - (n : ℤ) ≤ (a : ℤ) -
        (maxRootMult (cutPoly 1 0 P.1) : ℤ) := by
      simpa [ramifiedCutExponent, hweight] using hgrade
    have hltZ : (a : ℤ) < (maxRootMult (cutPoly 1 0 P.1) : ℤ) := by exact_mod_cast hlt
    exact ⟨hmin, by omega⟩

end Dixmier.Weyl
