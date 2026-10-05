/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.YAxisPositiveHorizontalMass
public import DixmierFormal.Weyl.GGVOriginalSubrectangularCases

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Complete horizontal dispatch for a Y-axis diagonal

The maximum-Y horizontal endpoint has minimal grade. Its negative case
uses crossing selection, its positive case uses Fourier and finite shear
descent, with zero-grade endpoints excluded by an explicit source premise.
-/
namespace Dixmier.Weyl

/-- A singleton Y-axis diagonal supplies the original member's case
alternative, with companion and uniform degree inputs explicit. -/
theorem preliminary_y_axis_diagonal_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (n : ℕ) (hdiag : totalDeg P.1 = n)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo 0 n)
    (hnozero : ∀ d ∈ (leadingForm 1 0 P.1).support, (∀ x ∈ (leadingForm 1 0 P.1).support, x 1 ≤ d 1) → grade d ≠ 0) :
    CaseAlternative P.1 := by
  classical
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 0
    (by norm_num [IsDirection])
  have hnonempty := MvPolynomial.support_nonempty.mpr
    (leadingForm_ne_zero_of_vDeg_pos P 1 0 hp)
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image
    (leadingForm 1 0 P.1).support (fun d => d 1) hnonempty
  have hdata := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) e).mp he
  have hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ e 0 := by
    intro d hd
    have hw := hdata.2 d hd
    simp [rationalNewtonWeight] at hw
    exact_mod_cast hw
  have hsame : ∀ d ∈ (symbol P.1).support, d 0 = e 0 → d 1 ≤ e 1 := by
    intro d hd heq
    apply hmax d
    apply (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) d).mpr
    refine ⟨hd,?_⟩
    intro c hc
    have hle := hx c hc
    simp [rationalNewtonWeight,heq]
    exact_mod_cast hle
  by_cases hneg : grade e < 0
  · exact preliminary_horizontal_negative_point_caseAlternative hsource P Q hpair ⟨e,he,hneg⟩
  · have hpos : 0 < grade e := by
      have hn := hnozero e he hmax
      omega
    have hexpo : expo (e 0) (e 1) = e := by
      ext i
      fin_cases i <;> simp [expo]
    apply preliminary_y_axis_positive_horizontal_caseAlternative hsource hdegree P Q hpair
      n (e 0) (e 1) hdiag hunique (hexpo.symm ▸ hdata.1) hx hsame
    dsimp [grade] at hpos
    omega

end Dixmier.Weyl
