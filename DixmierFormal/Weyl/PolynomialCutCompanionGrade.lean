/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionGradeAssembly
public import DixmierFormal.Weyl.PolynomialRamifiedCutEndpoint
public import DixmierFormal.Weyl.PolynomialCutCommonDirection
public import DixmierFormal.Weyl.PolynomialCutCommonWeights

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Transferring a source companion's cut grade to the polynomial pair

The ramified maximum-root theorem is applied to the actual lift of a
polynomial exact pair. The existing face identity then expresses its
strict negative grade in the paper's `cutPoly` coordinates.
-/

namespace Dixmier.Weyl

theorem exactPair_maxRoot_cut_grade_negative_of_source_companion
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hsum : 0 < ρ + σ)
    (hP : 0 < vDeg ρ σ P.1)
    (hPne : P ≠ 0)
    (hdirP : InDir ρ σ P.1)
    (hQP : Q*P-P*Q = 1)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P))
    (hface : ramifiedTopFacePolynomial l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P))
    (hFweight : ramifiedWeightDeg l hl ρ σ F = (l : ℤ)*(ρ+σ))
    (hcutDegree : 0 < (cutPoly ρ σ P.1).natDegree)
    (hOldEnd : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        ((cutPoly ρ σ P.1).natDegree : ℤ) < 0) :
    (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0 := by
  obtain ⟨d₁,_,hd₁,_,_⟩ := Finset.one_lt_card_iff.mp hdirP
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d₁
  let r : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ P.1
  have hpoint := polynomialRamifiedLift_face_point
    l hl P ρ σ hdiv i j hd₁
  have hupper : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r := by
    intro u n hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hu
  have hPweight : ramifiedWeightDeg l hl ρ σ
      (polynomialRamifiedLift l P) = ρ*r :=
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ (ρ*r)
      (polynomialRamifiedLift l P) ⟨_,hpoint.1,hpoint.2⟩
      (fun p hp => hupper p.1 p.2 hp)
  have htopFace : ramifiedTopFacePolynomial l hl ρ σ
      (polynomialRamifiedLift l P) = cutPoly ρ σ P.1 := by
    rw [ramifiedTopFacePolynomial_eq_cutFace l hl ρ σ hρ hdiv
      (polynomialRamifiedLift l P) r hPweight
      (by intro p hp; rw [hPweight]; exact hupper p.1 p.2 hp)]
    exact polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv
  have hPtopDegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ
      (polynomialRamifiedLift l P)).natDegree := by
    rw [htopFace]
    exact hcutDegree
  have hPne' : polynomialRamifiedLift l P ≠ 0 := by
    simpa [polynomialRamifiedLift_zero l hl] using
      (polynomialRamifiedLift_injective l hl).ne hPne
  have hcomm := polynomialRamifiedLift_bracket_one l hl P Q hQP
  have hrpos : 0 < ρ*r := by
    have hlz : (0 : ℤ) < l := by exact_mod_cast hl
    have hscale : ρ*r = (l : ℤ)*vDeg ρ σ P.1 := by
      dsimp [r]
      calc
        _ = (ρ*((l : ℤ)/ρ))*vDeg ρ σ P.1 := by ring
        _ = (l : ℤ)*vDeg ρ σ P.1 := by
          rw [Int.mul_ediv_cancel' hdiv]
    rw [hscale]
    exact mul_pos hlz hP
  have hOldEnd' : r - (ramifiedCutExponent l ρ σ + (l : ℤ)) *
      ((ramifiedFacePolynomial l hl (polynomialRamifiedLift l P) r
        (ramifiedCutExponent l ρ σ)).natDegree : ℤ) < 0 := by
    simpa only [r, polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]
      using hOldEnd
  obtain ⟨c,_,_,_,hneg⟩ :=
    ramifiedCutAut_exists_maxRoot_negative_grade_of_source_companion
      l hl ρ σ r ((l : ℤ)*(i : ℤ)) j hρ hdiv hsum hrpos
      (polynomialRamifiedLift l P) (polynomialRamifiedLift l Q) F
      hcomm hPne' hFne hpoint.1 hpoint.2 hupper
      hdegree hface hFweight hPtopDegree hOldEnd'
  simpa only [r,
    polynomialRamifiedFace_maxRootMult_eq_cutPoly l hl P ρ σ hρ hdiv]
    using hneg

/-- The source companion supplies the selected-grade premise of the
existing common-adjacent-face theorem for a polynomial exact pair. -/
theorem exactPair_maxRoot_cut_common_face_of_source_companion
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hPne : P ≠ 0)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q*P-P*Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P))
    (hface : ramifiedTopFacePolynomial l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P))
    (hFweight : ramifiedWeightDeg l hl ρ σ F = (l : ℤ)*(ρ+σ))
    (hcutDegree : 0 < (cutPoly ρ σ P.1).natDegree)
    (hOldEnd : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        ((cutPoly ρ σ P.1).natDegree : ℤ) < 0) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let rP := ((l : ℤ) / ρ) * vDeg ρ σ P.1
      let rQ := ((l : ℤ) / ρ) * vDeg ρ σ Q.1
      let M := (cutPoly ρ σ P.1).rootMultiplicity c
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      ∃ t : ℚ, 0 < t ∧
        t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
        (∀ p ∈ ramifiedPBWSupport l hl U,
          (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
            ((ρ*rP : ℤ) : ℚ) - t * (M : ℚ)) ∧
        (∀ q ∈ ramifiedPBWSupport l hl V,
          (ramifiedWeight l ρ σ q : ℚ) - t * (q.2 : ℚ) ≤
            ((ρ*rQ : ℤ) : ℚ) - t * (N : ℚ)) ∧
        (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
          (ramifiedWeight l ρ σ BP : ℚ) - t * (BP.2 : ℚ) =
            ((ρ*rP : ℤ) : ℚ) - t * (M : ℚ)) ∧
        (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
          (ramifiedWeight l ρ σ BQ : ℚ) - t * (BQ.2 : ℚ) =
            ((ρ*rQ : ℤ) : ℚ) - t * (N : ℚ)) := by
  have hgrade := exactPair_maxRoot_cut_grade_negative_of_source_companion
    l hl P Q ρ σ hρ hdiv hdir.2 hP hPne hdirP hQP
      F hFne hdegree hface hFweight hcutDegree hOldEnd
  exact exactPair_maxRoot_cut_exists_common_early_adjacent_face
    l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP
      hsum d n hd hn hweight hcop hgrade

/-- Under the source companion, the maximum-root cut reaches a
primitive common direction with positive weights and the same reduced
ratio. This is the geometric core of the cut, before the universal
forbidden-corner conclusion. -/
theorem exactPair_maxRoot_cut_positive_ratio_of_source_companion
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hPne : P ≠ 0)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q*P-P*Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (F : ramifiedOperatorAlgebra l) (hFne : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P))
    (hface : ramifiedTopFacePolynomial l hl ρ σ
      (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
        ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P))
    (hFweight : ramifiedWeightDeg l hl ρ σ F = (l : ℤ)*(ρ+σ))
    (hcutDegree : 0 < (cutPoly ρ σ P.1).natDegree)
    (hOldEnd : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        ((cutPoly ρ σ P.1).natDegree : ℤ) < 0) :
    ∃ c : ℂ, ∃ r s : ℤ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      IsDirection r s ∧ 0 < r ∧ (σ ≤ 0 → s < 0) ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let M := (cutPoly ρ σ P.1).rootMultiplicity c
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      let E : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
          ramifiedCutExponent l ρ σ*(M : ℤ),M)
      let G : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
          ramifiedCutExponent l ρ σ*(N : ℤ),N)
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s U ∧
      ramifiedWeight l r s G = ramifiedWeightDeg l hl r s V ∧
      0 < ramifiedWeightDeg l hl r s U ∧
      0 < ramifiedWeightDeg l hl r s V ∧
      ramifiedWeightDeg l hl r s V * (d : ℤ) =
        ramifiedWeightDeg l hl r s U * (n : ℤ) ∧
      E.1 - (l : ℤ)*(E.2 : ℤ) < 0 ∧
      G.1 - (l : ℤ)*(G.2 : ℤ) < 0 ∧
      (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
        ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s U) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
        ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s V) := by
  have hgrade := exactPair_maxRoot_cut_grade_negative_of_source_companion
    l hl P Q ρ σ hρ hdiv hdir.2 hP hPne hdirP hQP
      F hFne hdegree hface hFweight hcutDegree hOldEnd
  exact exactPair_maxRoot_cut_exists_common_face_positive_ratio
    l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP
      hsum d n hd hn hweight hcop hgrade

end Dixmier.Weyl
