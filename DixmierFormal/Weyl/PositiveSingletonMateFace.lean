/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveProportionalMateDescent
public import DixmierFormal.Weyl.GGVCompanionJosephFrontier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual proportional mate of a positive singleton face

Both mate endpoints lie on the source endpoint ray. Positive weights
identify them; the resulting rows feed the full paired finite descent.
-/
namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem counterexample_positive_singleton_proportional_mate
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b) :
    ∃ c d : ℕ, 0 < d ∧ a*d=b*c ∧
      (leadingForm 1 (σ : ℤ) Q.1).support = {expo c d} ∧
      vDeg 1 (σ : ℤ) Q.1 = ((c+σ*d : ℕ) : ℤ) := by
  classical
  have hdir : IsDirection 1 (σ : ℤ) := ⟨by simp,by positivity⟩
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 (σ : ℤ) hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 (σ : ℤ) hdir
  have hPdeg : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support,
      Finsupp.weight (wt 1 (σ : ℤ)) e = vDeg 1 (σ : ℤ) P.1 :=
    fun e he => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 (σ : ℤ)) (n := vDeg 1 (σ : ℤ) P.1)
      (MvPolynomial.mem_support_iff.mp he)
  have hQdeg : ∀ e ∈ (leadingForm 1 (σ : ℤ) Q.1).support,
      Finsupp.weight (wt 1 (σ : ℤ)) e = vDeg 1 (σ : ℤ) Q.1 :=
    fun e he => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt 1 (σ : ℤ)) (n := vDeg 1 (σ : ℤ) Q.1)
      (MvPolynomial.mem_support_iff.mp he)
  obtain ⟨u,v,r,t,hu,hv,hr,ht,hmax,hmin,_,_,hdu,hdv⟩ :=
    poisson_homogeneous_support_endpoints_collinear (wt 1 (σ : ℤ))
      (vDeg 1 (σ : ℤ) Q.1) (vDeg 1 (σ : ℤ) P.1)
      (leadingForm 1 (σ : ℤ) Q.1) (leadingForm 1 (σ : ℤ) P.1)
      (Or.inl (by simp [wt])) hQdeg hPdeg
      (leadingForm_ne_zero_of_vDeg_pos Q 1 (σ : ℤ) hq)
      (leadingForm_ne_zero_of_vDeg_pos P 1 (σ : ℤ) hp)
      (counterexample_leadingPoisson_zero_all_directions P Q hpair 1 (σ : ℤ) hdir)
  rw [hunique r hr] at hdu
  rw [hunique t ht] at hdv
  simp only [expo, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    zero_add, add_zero] at hdu hdv
  have hduN : a*(u 1)=b*(u 0) := by
    have hh := sub_eq_zero.mp hdu
    have hhN : (u 1)*a=(u 0)*b := by exact_mod_cast hh
    simpa [mul_comm] using hhN
  have hdvN : a*(v 1)=b*(v 0) := by
    have hh := sub_eq_zero.mp hdv
    have hhN : (v 1)*a=(v 0)*b := by exact_mod_cast hh
    simpa [mul_comm] using hhN
  have hduZ : (a : ℤ)*(u 1 : ℤ)=(b : ℤ)*(u 0 : ℤ) := by exact_mod_cast hduN
  have hdvZ : (a : ℤ)*(v 1 : ℤ)=(b : ℤ)*(v 0 : ℤ) := by exact_mod_cast hdvN
  have hwu : (u 0 : ℤ)+(σ : ℤ)*(u 1 : ℤ) = vDeg 1 (σ : ℤ) Q.1 := by
    simpa [wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,mul_comm] using hQdeg u hu
  have hwv : (v 0 : ℤ)+(σ : ℤ)*(v 1 : ℤ) = vDeg 1 (σ : ℤ) Q.1 := by
    simpa [wt,Finsupp.weight_eq_sum,Fin.sum_univ_two,mul_comm] using hQdeg v hv
  have hcoeff : 0 < (a : ℤ)+(σ : ℤ)*b := by
    have hs : 0 < (σ : ℤ) := by exact_mod_cast (by omega : 0 < σ)
    have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb
    positivity
  have hcancel : ((a : ℤ)+(σ : ℤ)*b)*((u 1 : ℤ)-v 1)=0 := by
    linear_combination (b : ℤ)*hwu-(b : ℤ)*hwv+hduZ-hdvZ
  have huy : (u 1 : ℤ)=v 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (ne_of_gt hcoeff))
  have huveq : u=v := by
    ext i
    fin_cases i
    · have hh : (u 0 : ℤ)=v 0 := by rw [huy] at hwu; omega
      exact_mod_cast hh
    · exact_mod_cast huy
  have heunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) Q.1).support, e=u := by
    intro e he
    have hlo := hmin e he
    rw [← huveq] at hlo
    exact exponent_eq_of_weights_eq_of_perp_eq (wt 1 (σ : ℤ))
      (Or.inl (by simp [wt])) ((hQdeg e he).trans (hQdeg u hu).symm)
      (le_antisymm (hmax e he) hlo)
  have huexpo : u=expo (u 0) (u 1) := by
    ext i
    fin_cases i <;> simp [expo]
  have hd : 0 < u 1 := by
    by_contra hn
    have hy : u 1=0 := by omega
    have hx : u 0=0 := by
      have hh : b*(u 0)=0 := by simpa [hy] using hduN.symm
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hb)
    simp [hx,hy] at hwu
    omega
  refine ⟨u 0,u 1,hd,hduN,?_,?_⟩
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_,?_⟩
    · rw [← huexpo]
      exact hu
    · intro e he
      exact (heunique e he).trans huexpo
  · simpa [Nat.cast_add,Nat.cast_mul] using hwu.symm

theorem counterexample_positive_singleton_finite_descent_pair
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) P.1).support, e = expo a b) :
    ∃ (c d : ℕ) (R S : A1 ℂ), 0 < d ∧ a*d=b*c ∧
      vDeg 1 (σ : ℤ) Q.1 = ((c+σ*d : ℕ) : ℤ) ∧
      IsCounterexamplePair R S ∧ totalDeg R.1=a+b ∧ totalDeg S.1=c+d := by
  obtain ⟨c,d,hd,hprop,hs,hw⟩ :=
    counterexample_positive_singleton_proportional_mate P Q hpair σ a b hσ hb hunique
  have hm : expo c d ∈ (leadingForm 1 (σ : ℤ) Q.1).support := by rw [hs]; simp
  have hy := preliminary_positive_last_point_y_bound ggv_preliminary_companion_proved
    Q (-P) (isCounterexamplePair_swap_neg P Q hpair) σ c d hσ hm
    (by
      intro e he
      have hh : e=expo c d := by simpa [hs] using he
      rw [hh]) hd
  obtain ⟨R,S,hRS,hR,hS⟩ := preliminary_positive_proportional_finite_descent_both_degrees
    ggv_preliminary_companion_proved P Q hpair σ a b c d hσ hb hmem hunique hy
    (polynomialFace_point_source_data Q 1 (σ : ℤ) c d hm).1 hprop
  exact ⟨c,d,R,S,hd,hprop,hw,hRS,hR,hS⟩

end Dixmier.Weyl
