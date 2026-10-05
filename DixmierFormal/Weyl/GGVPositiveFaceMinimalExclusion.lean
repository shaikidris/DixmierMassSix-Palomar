/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVProportionalDescentExclusion
public import DixmierFormal.Weyl.PositiveShearMonomialFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Degree minimality excludes genuine positive faces

The same polynomial root shear is applied to both operators. Inverting
the mate's cut translation recovers its original axis coefficient and
total degree, so the proportional paired descent contradicts minimality.
-/
namespace Dixmier.Weyl
open Polynomial

theorem positive_cut_constant_totalDeg
    (P : A1 ℂ) (σ N : ℕ) (hσ : 1 ≤ σ)
    (hw : vDeg 1 (σ : ℤ) P.1 = (N : ℤ))
    (hc : (cutPoly 1 (σ : ℤ) P.1).coeff 0 ≠ 0) :
    totalDeg P.1 = N := by
  have hface : expo N 0 ∈ (leadingForm 1 (σ : ℤ) P.1).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [← cutPoly_coeff_at_face_point P 1 (σ : ℤ) N 0 (by norm_num)
      (by simpa using hw.symm)]
    exact hc
  have hmax := (leadingForm_mem_iff_rational_slope P 1 (σ : ℤ)
    (by norm_num) (expo N 0)).mp hface
  apply totalDeg_eq_of_support_sum_bound P N 0 hmax.1
  intro e he
  have hh := hmax.2 e he
  have hhQ : (e 0 : ℚ)+(σ : ℚ)*(e 1 : ℚ) ≤ N := by
    simpa [rationalNewtonWeight,expo] using hh
  have hs : (1 : ℚ) ≤ σ := by exact_mod_cast hσ
  have hsum : (e 0 : ℚ)+(e 1 : ℚ) ≤ N := by
    nlinarith [show (0 : ℚ) ≤ e 1 by positivity]
  exact_mod_cast hsum

theorem polynomial_cut_inverse_translation
    (p q : ℂ[X]) (α : ℂ) (ht : q = p.comp (X+C α)) :
    p = q.comp (X-C α) := by
  rw [ht,Polynomial.comp_assoc]
  simp only [add_comp,X_comp,C_comp]
  simp

set_option maxHeartbeats 1000000 in
theorem degreeMinimal_positive_face_impossible
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (σ : ℕ) (hσ : 1 < σ)
    (hface : InDir 1 (σ : ℤ) P.1) : False := by
  classical
  have hpair := hmin.1
  obtain ⟨lam,α,a,b,hlam,hα,hb,hwP,hfP⟩ :=
    preliminary_positive_face_binomial ggv_preliminary_companion_proved
      P Q hpair σ hσ hface
  have hcP := positive_binomial_face_cut P σ a b lam α hfP
  obtain ⟨R,S,hRS,hR,hS⟩ :=
    polynomial_monomial_cut_recovers_polynomial_counterexample σ α P Q hpair
  have hdir : IsDirection 1 (σ : ℤ) := ⟨by simp,by positivity⟩
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 (σ : ℤ) hdir
  have hr := counterexample_vDeg_pos_all_directions R S hRS 1 (σ : ℤ) hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 (σ : ℤ) hdir
  have hs := counterexample_vDeg_pos_all_directions S (-R)
    (isCounterexamplePair_swap_neg R S hRS) 1 (σ : ℤ) hdir
  have hPne : P ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val hpair.1
    rw [hz] at hh
    simp at hh
  have hQne : Q ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val hpair.1
    rw [hz] at hh
    simp at hh
  obtain ⟨hwR,hcutR⟩ := polynomial_monomial_cut_weight_and_translate
    P R σ α hPne hp hr hR
  have hRcut : cutPoly 1 (σ : ℤ) R.1 = C lam * X^b := by
    rw [hcutR,hcP]
    simp only [mul_comp,pow_comp,sub_comp,X_comp,C_comp]
    simp
  have hRface : leadingForm 1 (σ : ℤ) R.1 =
      MvPolynomial.C lam * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b := by
    have hh := positive_face_eq_of_linear_power_cut R lam 0 σ a b
      (hwR.trans hwP) (by simpa using hRcut)
    simpa using hh
  have hRsupport : (leadingForm 1 (σ : ℤ) R.1).support = {expo a b} := by
    rw [hRface]
    exact weighted_monomial_support lam hlam a b
  have hRunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) R.1).support, e=expo a b := by
    intro e he
    simpa [hRsupport] using he
  obtain ⟨c,d,hd,_,hSsupport,hwS⟩ :=
    counterexample_positive_singleton_proportional_mate R S hRS
      σ a b (by omega) (by omega) hRunique
  let mu := MvPolynomial.coeff (expo c d) (leadingForm 1 (σ : ℤ) S.1)
  have hmu : mu ≠ 0 := MvPolynomial.mem_support_iff.mp (by rw [hSsupport]; simp)
  have hSmono : leadingForm 1 (σ : ℤ) S.1 =
      MvPolynomial.C mu * MvPolynomial.X 0 ^ c * MvPolynomial.X 1 ^ d := by
    have hh := MvPolynomial.eq_monomial_of_support_subset_singleton
      (φ := leadingForm 1 (σ : ℤ) S.1) (d₀ := expo c d)
      (by intro e he; simpa [hSsupport] using he)
    rw [hh,MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.monomial_add_single]
    rfl
  have hScut : cutPoly 1 (σ : ℤ) S.1 = C mu * X^d := by
    simpa using positive_binomial_face_cut S σ c d mu 0 (by simpa using hSmono)
  obtain ⟨hwQ,hcutS⟩ := polynomial_monomial_cut_weight_and_translate
    Q S σ α hQne hq hs hS
  have hQcut : cutPoly 1 (σ : ℤ) Q.1 = C mu * (X-C α)^d := by
    rw [polynomial_cut_inverse_translation _ _ α hcutS,hScut]
    simp only [mul_comp,pow_comp,X_comp,C_comp]
  have hQconstant : (cutPoly 1 (σ : ℤ) Q.1).coeff 0 ≠ 0 := by
    rw [hQcut]
    simpa only [coeff_zero_eq_eval_zero,eval_mul,eval_C,eval_pow,eval_sub,
      eval_X,zero_sub] using mul_ne_zero hmu (pow_ne_zero d (neg_ne_zero.mpr hα))
  have hQtotal := positive_cut_constant_totalDeg Q σ (c+σ*d) (by omega)
    (hwQ.symm.trans hwS) hQconstant
  have hPtotal := (preliminary_positive_face_total_degree_axis_endpoint
    ggv_preliminary_companion_proved P Q hpair 1 σ (by norm_num) hσ
    (by simp) hdir hface).2.1
  norm_num only [Nat.cast_one] at hPtotal
  apply degreeMinimal_proportional_positive_descent_impossible P Q R S hmin hRS
    σ a b hσ (by omega)
  · rw [hPtotal,hwP]
    omega
  · rw [hQtotal,hwS]
    omega
  · rw [hRsupport]
    simp
  · exact hRunique

theorem degreeMinimal_diagonal_axis_singleton_impossible
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (n : ℕ) (hmem : expo n 0 ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 1 P.1).support, e=expo n 0) : False := by
  obtain ⟨σ,hσ,hface,_⟩ := preliminary_axis_diagonal_positive_face
    ggv_preliminary_companion_proved P Q hmin.1 n hmem hunique
  exact degreeMinimal_positive_face_impossible P Q hmin σ hσ hface

end Dixmier.Weyl
