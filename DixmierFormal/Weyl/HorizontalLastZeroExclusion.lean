/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.YAxisCaseDispatch

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Nonzero grade at the maximum-Y horizontal endpoint

Fourier makes this endpoint the maximal-grade point of the vertical face,
where the preliminary companion's diagonal obstruction applies.
-/
namespace Dixmier.Weyl

/-- A maximum-Y horizontal endpoint cannot have grade zero. -/
theorem preliminary_horizontal_max_y_grade_ne_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (leadingForm 1 0 P.1).support)
    (hmax : ∀ d ∈ (leadingForm 1 0 P.1).support, d 1 ≤ e 1) :
    grade e ≠ 0 := by
  classical
  intro hz
  have hdiag : e 0 = e 1 := by dsimp [grade] at hz; omega
  have hexpo : expo (e 0) (e 1) = e := by ext i; fin_cases i <;> simp [expo]
  have hdata := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) e).mp he
  have hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ e 0 := by
    intro d hd
    have hw := hdata.2 d hd
    simp [rationalNewtonWeight] at hw
    exact_mod_cast hw
  have hy : ∀ d ∈ (symbol P.1).support, d 0 = e 0 → d 1 ≤ e 1 := by
    intro d hd heq
    apply hmax d
    apply (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) d).mpr
    refine ⟨hd,?_⟩
    intro c hc
    have hle := hx c hc
    simp [rationalNewtonWeight,heq]
    exact_mod_cast hle
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 0
    (by norm_num [IsDirection])
  have hw := (polynomialFace_point_source_data P 1 0 (e 0) (e 1)
    (hexpo.symm ▸ he)).2
  have ha : 0 < e 0 := by norm_num at hw; rw [← hw] at hp; exact_mod_cast hp
  let T := fourierAlgHom ℂ P
  have hpoint := fourier_rightmost_column_endpoint_mem P (e 0) (e 1) ha
    (hexpo.symm ▸ hdata.1) hx hy
  obtain ⟨hFy,hFx⟩ := fourier_rightmost_column_boundary_bounds P (e 0) (e 1) hx hy
  have hvertical : expo (e 1) (e 0) ∈ (leadingForm 0 1 T.1).support := by
    apply (leadingForm_mem_iff_realExposedFace 0 1 T.1 _).mpr
    refine ⟨hpoint,?_⟩
    intro d hd
    have hle := hFy d hd
    simp [realNewtonWeight,expo]
    exact_mod_cast hle
  have hgradeMax : ∀ d ∈ (leadingForm 0 1 T.1).support,
      Finsupp.weight (wt 1 (-1)) d ≤ Finsupp.weight (wt 1 (-1)) (expo (e 1) (e 0)) := by
    intro d hd
    have hddata := (leadingForm_mem_iff_realExposedFace 0 1 T.1 d).mp hd
    have hle := hFy d hddata.1
    have hback := hddata.2 (expo (e 1) (e 0)) hpoint
    simp [realNewtonWeight,expo] at hback
    have heq : d 1 = e 0 := by omega
    have hdx := hFx d hddata.1 heq
    simp [wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,expo,heq]
    exact_mod_cast hdx
  exact ggv_preliminary_no_diagonal_leading_top hsource T (fourierAlgHom ℂ Q)
    (isCounterexamplePair_fourier P Q hpair) 0 1 (by norm_num [IsDirection])
    hvertical hgradeMax (by simp [expo,hdiag]) (by simpa [expo,hdiag] using ha)

/-- The Y-axis case dispatch uses no additional endpoint-grade premise. -/
theorem preliminary_y_axis_diagonal_caseAlternative_of_companion
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (n : ℕ) (hdiag : totalDeg P.1 = n)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo 0 n) :
    CaseAlternative P.1 :=
  preliminary_y_axis_diagonal_caseAlternative hsource hdegree P Q hpair n hdiag hunique
    (preliminary_horizontal_max_y_grade_ne_zero hsource P Q hpair)

end Dixmier.Weyl
