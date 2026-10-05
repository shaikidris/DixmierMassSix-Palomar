/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveShearTerminalMateDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Terminal degrees for proportional positive endpoints

An occupied top-row endpoint on the first diagonal determines the mate
endpoint ray. Retained row bounds and proportionality determine both
terminal degrees, including a nonzero first-axis exponent.
-/
namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem counterexample_proportional_top_rows_mate_totalDeg
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) (a b c d : ℕ)
    (hb : 0 < b) (hdegree : totalDeg P.1 = a+b)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hPbound : ∀ e ∈ (symbol P.1).support, e 1 ≤ b)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support)
    (hprop : a*d=b*c) : totalDeg Q.1 = c+d := by
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1 hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 1 hdir
  have hPweight : vDeg 1 1 P.1 = ((a+b : ℕ) : ℤ) := by
    rw [← totalDeg_eq_vDeg_one_one P hp,hdegree]
  have hPface := support_totalDeg_mem_diagonal_leadingForm P (expo a b) hpoint
    (by simpa [expo] using hdegree.symm)
  have hPdeg : ∀ e ∈ (leadingForm 1 1 P.1).support,
      Finsupp.weight (wt 1 1) e = vDeg 1 1 P.1 :=
    fun e he => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 1) (n := vDeg 1 1 P.1)
      (MvPolynomial.mem_support_iff.mp he)
  have hQdeg : ∀ e ∈ (leadingForm 1 1 Q.1).support,
      Finsupp.weight (wt 1 1) e = vDeg 1 1 Q.1 :=
    fun e he => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt 1 1) (n := vDeg 1 1 Q.1)
      (MvPolynomial.mem_support_iff.mp he)
  have hbr : poisson (leadingForm 1 1 P.1) (leadingForm 1 1 Q.1) = 0 := by
    have hzero := counterexample_leadingPoisson_zero_all_directions P Q hpair 1 1 hdir
    unfold poisson at hzero ⊢
    linear_combination -hzero
  obtain ⟨_,x,_,y,_,hx,_,hy,_,hmin,_,_,_,hdet⟩ :=
    poisson_homogeneous_support_endpoints_collinear (wt 1 1)
      (vDeg 1 1 P.1) (vDeg 1 1 Q.1)
      (leadingForm 1 1 P.1) (leadingForm 1 1 Q.1)
      (Or.inl (by simp [wt])) hPdeg hQdeg
      (leadingForm_ne_zero_of_vDeg_pos P 1 1 hp)
      (leadingForm_ne_zero_of_vDeg_pos Q 1 1 hq)
      hbr
  have hsum : (x 0 : ℤ)+x 1 = (a : ℤ)+b := by
    simpa [hPweight,wt,Finsupp.weight_eq_sum,Fin.sum_univ_two] using hPdeg x hx
  have hperp := hmin (expo a b) hPface
  have hperp' : (x 0 : ℤ)-x 1 ≤ (a : ℤ)-b := by
    simp [perpWeight,wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,expo] at hperp
    omega
  have hxsource : x ∈ (symbol P.1).support :=
    (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) x).mp hx |>.1
  have hxb := hPbound x hxsource
  have hx0 : x 0 = a := by omega
  have hx1 : x 1 = b := by omega
  rw [hx0,hx1] at hdet
  have hdetN : b*(y 0) = a*(y 1) := by
    have hh := sub_eq_zero.mp hdet
    exact_mod_cast hh
  have hydeg : (y 0 : ℤ)+y 1 = vDeg 1 1 Q.1 := by
    simpa [wt,Finsupp.weight_eq_sum,Fin.sum_univ_two] using hQdeg y hy
  have hydegree : totalDeg Q.1 = y 0+y 1 := by
    have hh := (totalDeg_eq_vDeg_one_one Q hq).trans hydeg.symm
    exact_mod_cast hh
  have hysource : y ∈ (symbol Q.1).support :=
    (leadingForm_mem_iff_rational_slope Q 1 1 (by norm_num) y).mp hy |>.1
  have hyd := hQbound y hysource
  have hle : totalDeg Q.1 ≤ c+d := by
    rw [hydegree]
    nlinarith [hprop,hdetN]
  have hge := MvPolynomial.le_totalDegree hQpoint
  rw [Finsupp.sum_fintype (expo c d) (fun _ n => n) (by simp)] at hge
  have hge' : c+d ≤ totalDeg Q.1 := by
    simpa [totalDeg,expo,Fin.sum_univ_two] using hge
  exact Nat.le_antisymm hle hge'

theorem preliminary_positive_singleton_finite_descent_both_rows
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b c d : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧ totalDeg R.1 = a+b ∧
      expo a b ∈ (symbol R.1).support ∧
      (∀ e ∈ (symbol R.1).support, e 1 ≤ b) ∧
      (∀ e ∈ (symbol S.1).support, e 1 ≤ d) ∧
      expo c d ∈ (symbol S.1).support := by
  classical
  induction σ using Nat.strong_induction_on generalizing P Q with
  | h σ ih =>
    by_cases hbad : ∃ e ∈ (symbol P.1).support, a+b < e 0+e 1
    · obtain ⟨τ,R,S,hτ,hsmall,hRS,hface,hSbound,hSpoint⟩ :=
        preliminary_positive_descent_shear_step_with_mate_row hsource P Q hpair
          σ a b c d hσ hb hmem hunique hbad hQbound hQpoint
      exact ih τ hsmall R S hRS (by omega)
        (by rw [hface]; simp) (by intro e he; simpa [hface] using he)
        hSbound hSpoint
    · have hy := preliminary_positive_last_point_y_bound hsource P Q hpair σ a b hσ
        hmem (by intro e he; rw [hunique e he]) hb
      refine ⟨P,Q,hpair,totalDeg_eq_of_support_sum_bound P a b
        (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).1 ?_,
        (polynomialFace_point_source_data P 1 (σ : ℤ) a b hmem).1,hy,hQbound,hQpoint⟩
      intro e he
      by_contra hn
      exact hbad ⟨e,he,by omega⟩

theorem preliminary_positive_proportional_finite_descent_both_degrees
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b c d : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support) (hprop : a*d=b*c) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      totalDeg R.1 = a+b ∧ totalDeg S.1 = c+d := by
  obtain ⟨R,S,hRS,hR,hRpoint,hRbound,hSbound,hSpoint⟩ :=
    preliminary_positive_singleton_finite_descent_both_rows hsource P Q hpair
      σ a b c d hσ hb hmem hunique hQbound hQpoint
  exact ⟨R,S,hRS,hR,counterexample_proportional_top_rows_mate_totalDeg
    R S hRS a b c d hb hR hRpoint hRbound hSbound hSpoint hprop⟩

end Dixmier.Weyl
