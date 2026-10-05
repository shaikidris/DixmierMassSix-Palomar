/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCompanionOperatorLift
public import DixmierFormal.Weyl.PolynomialCutCompanionGrade

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!+# Polynomial companions supply the ramified cut hypotheses

The preliminary companion input supplies a finite polynomial Weyl operator.
Its nonzero leading bracket computes the actual commutator degree and face.
The faithful ramified lift preserves both quantities, so the maximum-root
grade theorem needs no independently supplied ramified companion witness.
The preliminary companion itself remains a source obligation.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Positive source weight is scaled by the coefficient index in the
faithful polynomial-to-ramified lift. -/
theorem polynomialRamifiedLift_weightDeg_eq_of_pos
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < vDeg ρ σ P.1) :
    ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P) =
      (l : ℤ) * vDeg ρ σ P.1 := by
  have hne := leadingForm_ne_zero_of_vDeg_pos P ρ σ hpos
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hne
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective e
  have hpoint := polynomialRamifiedLift_face_point l hl P ρ σ hdiv i j he
  have hscale : ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) =
      (l : ℤ) * vDeg ρ σ P.1 := by
    rw [← mul_assoc, Int.mul_ediv_cancel' hdiv]
  apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ
    ((l : ℤ) * vDeg ρ σ P.1)
  · exact ⟨_, hpoint.1, hpoint.2.trans hscale⟩
  · intro p hp
    exact (polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv p.1 p.2 hp).trans_eq hscale

/-- The ramified top-face polynomial of a positive-weight source lift
is exactly the paper's polynomial cut face. -/
theorem polynomialRamifiedLift_topFace_eq_cutPoly_of_pos
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < vDeg ρ σ P.1) :
    ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P) =
      cutPoly ρ σ P.1 := by
  have hweight := polynomialRamifiedLift_weightDeg_eq_of_pos
    l hl P ρ σ hρ hdiv hpos
  have hscale : (l : ℤ) * vDeg ρ σ P.1 =
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    rw [← mul_assoc, Int.mul_ediv_cancel' hdiv]
  rw [ramifiedTopFacePolynomial_eq_cutFace l hl ρ σ hρ hdiv
    (polynomialRamifiedLift l P) (((l : ℤ) / ρ) * vDeg ρ σ P.1)
    (hweight.trans hscale) (by
      intro p hp
      rw [hweight, hscale]
      exact polynomialRamifiedLift_weight_le_scaled_vDeg
        l hl P ρ σ hdiv p.1 p.2 hp)]
  exact polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv

/-- The preliminary source input yields an actual finite ramified
companion with the exact degree and bracket-face contracts of the cut. -/
theorem preliminary_companion_has_polynomial_cut_witness
    (hsource : GGVPreliminaryCompanionInput)
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q) (ρ σ : ℤ)
    (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ)) :
    ∃ T : A1 ℂ, T ≠ 0 ∧
      ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l T) = (l : ℤ) * (ρ + σ) ∧
      ramifiedWeightDeg l hl ρ σ
        (polynomialRamifiedLift l P * polynomialRamifiedLift l T - polynomialRamifiedLift l T * polynomialRamifiedLift l P) =
          ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P) ∧
      ramifiedTopFacePolynomial l hl ρ σ
        (polynomialRamifiedLift l P * polynomialRamifiedLift l T - polynomialRamifiedLift l T * polynomialRamifiedLift l P) =
          ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P) := by
  obtain ⟨T, hTdeg, hThom, hbr⟩ :=
    ggv_operator_preliminary_of_symbol_input hsource P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hTpos : 0 < vDeg ρ σ T.1 := by rw [hTdeg]; exact hdir.2
  have hTface : leadingForm ρ σ T.1 = symbol T.1 := by
    unfold leadingForm
    rw [hTdeg]
    exact weightedHomogeneousComponent_eq_self (w := wt ρ σ) hThom
  have hfixed := preliminary_companion_symbol_of_operator
    P T ρ σ hdir.2 hPpos hTdeg hThom hbr
  have hpoisson : poisson (leadingForm ρ σ P.1) (leadingForm ρ σ T.1) =
      leadingForm ρ σ P.1 := by rw [hTface]; exact hfixed
  have hnonzero : poisson (leadingForm ρ σ P.1)
      (leadingForm ρ σ T.1) ≠ 0 := by
    rw [hpoisson]
    exact leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos
  obtain ⟨hBdeg, hBface⟩ := leadingForm_commutator T P ρ σ hdir.2 hnonzero
  have hdegree : vDeg ρ σ (P*T-T*P : A1 ℂ).1 = vDeg ρ σ P.1 := by
    rw [hTdeg] at hBdeg
    omega
  have hface : leadingForm ρ σ (P*T-T*P : A1 ℂ).1 =
      leadingForm ρ σ P.1 := hBface.trans hpoisson
  have hBpos : 0 < vDeg ρ σ (P*T-T*P : A1 ℂ).1 := by
    rw [hdegree]; exact hPpos
  have hTne : T ≠ 0 := by
    intro hz
    have hzero : symbol T.1 = 0 := by
      rw [hz]
      exact (symbolLinearMap (K := ℂ)).map_zero
    rw [hzero] at hfixed
    have hPzero : leadingForm ρ σ P.1 = 0 := by
      simpa [poisson] using hfixed.symm
    exact (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos) hPzero
  have hFne : polynomialRamifiedLift l T ≠ 0 := by
    simpa [polynomialRamifiedLift_zero l hl] using
      (polynomialRamifiedLift_injective l hl).ne hTne
  refine ⟨T, hTne, ?_, ?_, ?_⟩
  · rw [polynomialRamifiedLift_weightDeg_eq_of_pos l hl T ρ σ hρ hdiv hTpos,
      hTdeg]
  · rw [← polynomialRamifiedLift_commutator l hl T P,
      polynomialRamifiedLift_weightDeg_eq_of_pos l hl (P*T-T*P) ρ σ hρ hdiv hBpos,
      polynomialRamifiedLift_weightDeg_eq_of_pos l hl P ρ σ hρ hdiv hPpos,
      hdegree]
  · rw [← polynomialRamifiedLift_commutator l hl T P,
      polynomialRamifiedLift_topFace_eq_cutPoly_of_pos l hl (P*T-T*P)
        ρ σ hρ hdiv hBpos,
      polynomialRamifiedLift_topFace_eq_cutPoly_of_pos l hl P ρ σ hρ hdiv hPpos]
    simp only [cutPoly, hface]

theorem preliminary_companion_has_ramified_cut_witness
    (hsource : GGVPreliminaryCompanionInput)
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q) (ρ σ : ℤ)
    (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ)) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      ramifiedWeightDeg l hl ρ σ F = (l : ℤ) * (ρ + σ) ∧
      ramifiedWeightDeg l hl ρ σ
        (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
          ramifiedWeightDeg l hl ρ σ (polynomialRamifiedLift l P) ∧
      ramifiedTopFacePolynomial l hl ρ σ
        (polynomialRamifiedLift l P * F - F * polynomialRamifiedLift l P) =
          ramifiedTopFacePolynomial l hl ρ σ (polynomialRamifiedLift l P) := by
  obtain ⟨T, hTne, hweight, hdegree, hface⟩ :=
    preliminary_companion_has_polynomial_cut_witness hsource l hl P Q hpair ρ σ hdir hρ hdiv
  have hFne : polynomialRamifiedLift l T ≠ 0 := by
    simpa [polynomialRamifiedLift_zero l hl] using
      (polynomialRamifiedLift_injective l hl).ne hTne
  exact ⟨polynomialRamifiedLift l T, hFne, hweight, hdegree, hface⟩

/-- The polynomial source companion suffices for the maximum-root
negative-grade conclusion. The ramified witness is constructed internally. -/
theorem preliminary_companion_maxRoot_cut_grade_negative
    (hsource : GGVPreliminaryCompanionInput)
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q) (ρ σ : ℤ)
    (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ)) (hdirP : InDir ρ σ P.1)
    (hcutDegree : 0 < (cutPoly ρ σ P.1).natDegree)
    (hOldEnd : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        ((cutPoly ρ σ P.1).natDegree : ℤ) < 0) :
    (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0 := by
  obtain ⟨F, hFne, hFweight, hdegree, hface⟩ :=
    preliminary_companion_has_ramified_cut_witness
      hsource l hl P Q hpair ρ σ hdir hρ hdiv
  have hPne : P ≠ 0 := by
    intro hz
    have hcomm := hpair.1
    rw [hz] at hcomm
    have hcommOp := congrArg Subtype.val hcomm
    simp at hcommOp
  exact exactPair_maxRoot_cut_grade_negative_of_source_companion
    l hl P Q ρ σ hρ hdiv hdir.2
    (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)
    hPne hdirP hpair.1 F hFne hdegree hface hFweight hcutDegree hOldEnd

end Dixmier.Weyl
