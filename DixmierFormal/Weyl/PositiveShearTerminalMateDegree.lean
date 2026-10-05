/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveShearMateDescent

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Both terminal degrees in a pure-axis positive descent

An occupied pure-Y diagonal point forces the mate's corresponding
endpoint onto that axis. A preserved occupied top row then determines
the mate's total degree exactly.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem counterexample_y_axis_top_point_mate_totalDeg
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) (b c d : ℕ)
    (hb : 0 < b) (hdegree : totalDeg P.1 = b)
    (hpoint : expo 0 b ∈ (symbol P.1).support)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo c d ∈ (symbol Q.1).support) :
    totalDeg Q.1 = d ∧ c = 0 := by
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1 hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 1 hdir
  have hPweight : vDeg 1 1 P.1 = (b : ℤ) := by
    rw [← totalDeg_eq_vDeg_one_one P hp,hdegree]
  have hPface := support_totalDeg_mem_diagonal_leadingForm P (expo 0 b) hpoint
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
  have hsum : (x 0 : ℤ)+x 1 = b := by
    simpa [hPweight,wt,Finsupp.weight_eq_sum,Fin.sum_univ_two] using hPdeg x hx
  have hperp := hmin (expo 0 b) hPface
  have hperp' : (x 0 : ℤ)-x 1 ≤ -(b : ℤ) := by
    simpa [perpWeight,wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,expo] using hperp
  have hx0 : x 0 = 0 := by omega
  have hx1 : x 1 = b := by omega
  have hy0 : y 0 = 0 := by
    rw [hx0,hx1] at hdet
    have hz : (b : ℂ)*(y 0 : ℂ) = 0 := by simpa using hdet
    have hbn : (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    have hzero := (mul_eq_zero.mp hz).resolve_left hbn
    exact_mod_cast hzero
  have hydeg : (y 1 : ℤ) = vDeg 1 1 Q.1 := by
    simpa [wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,hy0] using hQdeg y hy
  have hydegree : totalDeg Q.1 = y 1 := by
    have hh := (totalDeg_eq_vDeg_one_one Q hq).trans hydeg.symm
    exact_mod_cast hh
  have hysource : y ∈ (symbol Q.1).support := by
    exact (leadingForm_mem_iff_rational_slope Q 1 1 (by norm_num) y).mp hy |>.1
  have hle : totalDeg Q.1 ≤ d := by rw [hydegree]; exact hQbound y hysource
  have hge := MvPolynomial.le_totalDegree hQpoint
  rw [Finsupp.sum_fintype (expo c d) (fun _ n => n) (by simp)] at hge
  have hge' : c+d ≤ totalDeg Q.1 := by
    simpa [totalDeg,expo,Fin.sum_univ_two] using hge
  constructor <;> omega

theorem preliminary_positive_axis_finite_descent_both_degrees
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ b d : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo 0 b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo 0 b)
    (hQbound : ∀ e ∈ (symbol Q.1).support, e 1 ≤ d)
    (hQpoint : expo 0 d ∈ (symbol Q.1).support) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      totalDeg R.1 = b ∧ totalDeg S.1 = d := by
  obtain ⟨R,S,hRS,hRdegree,hRpoint,hSbound,hSpoint⟩ :=
    preliminary_positive_singleton_finite_descent_with_mate_row hsource
      P Q hpair σ 0 b 0 d hσ hb hmem hunique hQbound hQpoint
  have hRb : totalDeg R.1 = b := by simpa using hRdegree
  exact ⟨R,S,hRS,hRb,(counterexample_y_axis_top_point_mate_totalDeg R S hRS
    b 0 d hb hRb hRpoint hSbound hSpoint).1⟩

end Dixmier.Weyl
