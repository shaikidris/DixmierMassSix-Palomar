/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPureLinearMinimalExclusion
public import DixmierFormal.Weyl.FourierDiagonalEndpoints

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Occupied proportional rectangles for every minimal pair

A common linear shear gives a nonzero axis coefficient of the diagonal
cut. Fourier exchange turns that coefficient into the highest cut term.
The complete root classification then reduces to two distinct roots,
whose exact standardization preserves both degrees and minimality.
-/
namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 1000000

theorem degreeMinimal_full_degree_diagonal_cut_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      (cutPoly 1 1 R.1).natDegree = totalDeg R.1 := by
  classical
  have hne := counterexample_diagonal_cut_ne_zero P Q hmin.1
  have hex : ∃ c : ℂ, (cutPoly 1 1 P.1).eval c ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply Polynomial.funext
    intro x
    simpa using hn x
  obtain ⟨c,hc⟩ := hex
  obtain ⟨A,B,hminAB,hAdeg,hBdeg,hAcut,_,_,_⟩ :=
    degreeMinimal_linear_cut_recovers_pair P Q c hmin
  have hconstant : (cutPoly 1 1 A.1).coeff 0 ≠ 0 := by
    rw [hAcut]
    simpa only [coeff_zero_eq_eval_zero,eval_comp,eval_add,eval_X,eval_C,zero_add]
      using hc
  have hp := counterexample_vDeg_pos_all_directions A B hminAB.1 1 1
    (by norm_num [IsDirection])
  have hwA : vDeg 1 1 A.1 = (totalDeg A.1 : ℤ) :=
    (totalDeg_eq_vDeg_one_one A hp).symm
  have haxis : expo (totalDeg A.1) 0 ∈ (leadingForm 1 1 A.1).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [← cutPoly_coeff_at_face_point A 1 1 (totalDeg A.1) 0 (by norm_num)
      (by simpa using hwA.symm)]
    exact hconstant
  let R := fourierAlgHom ℂ A
  let S := fourierAlgHom ℂ B
  have hminRS : IsDegreeMinimalCounterexamplePair R S :=
    degreeMinimal_fourier_preserved A B hminAB
  have hpoint : expo 0 (totalDeg R.1) ∈ (leadingForm 1 1 R.1).support := by
    have hh := fourier_diagonal_point_mem A (expo (totalDeg A.1) 0) haxis
    simpa [R,totalDeg_fourier_eq,expo] using hh
  have hpR := counterexample_vDeg_pos_all_directions R S hminRS.1 1 1
    (by norm_num [IsDirection])
  have hwR : vDeg 1 1 R.1 = (totalDeg R.1 : ℤ) :=
    (totalDeg_eq_vDeg_one_one R hpR).symm
  have hcoeff : (cutPoly 1 1 R.1).coeff (totalDeg R.1) ≠ 0 := by
    rw [cutPoly_coeff_at_face_point R 1 1 0 (totalDeg R.1) (by norm_num)
      (by simpa using hwR.symm)]
    exact MvPolynomial.mem_support_iff.mp hpoint
  refine ⟨R,S,hminRS,?_,?_,?_⟩
  · exact (totalDeg_fourier_eq A).trans hAdeg
  · exact (totalDeg_fourier_eq B).trans hBdeg
  · exact Nat.le_antisymm (diagonal_cut_natDegree_le R (totalDeg R.1) hwR)
      (le_natDegree_of_ne_zero hcoeff)

theorem degreeMinimal_subrectangular_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ (R S : A1 ℂ) (a b u v : ℕ),
      IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < a ∧ 0 < b ∧ 0 < u ∧ 0 < v ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧ a*v=b*u := by
  obtain ⟨R,S,hminRS,hRdeg,hSdeg,hfull⟩ :=
    degreeMinimal_full_degree_diagonal_cut_pair P Q hmin
  rcases preliminary_diagonal_cut_factorization ggv_preliminary_companion_proved
      R S hminRS.1 with
    ⟨lam,hlam,hcut⟩ | ⟨lam,α,k,hlam,hk,hcut⟩ |
    ⟨lam,α,β,a,b,hlam,hab,ha,hb,hcut⟩
  · have hz : totalDeg R.1 = 0 := by
      rw [hcut] at hfull
      simpa using hfull.symm
    have hp := counterexample_vDeg_pos_all_directions R S hminRS.1 1 1
      (by norm_num [IsDirection])
    have hw := totalDeg_eq_vDeg_one_one R hp
    rw [hz] at hw
    omega
  · have hdegree : totalDeg R.1 = k := by
      rw [hcut,natDegree_C_mul hlam,natDegree_pow,natDegree_X_sub_C] at hfull
      simpa using hfull.symm
    exact False.elim (degreeMinimal_pure_linear_diagonal_impossible
      R S hminRS lam α k hlam hdegree hcut)
  · have hdegree : totalDeg R.1 = a+b := by
      rw [hcut,natDegree_mul
        (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero a (X_sub_C_ne_zero α)))
        (pow_ne_zero b (X_sub_C_ne_zero β)),natDegree_C_mul hlam,
        natDegree_pow,natDegree_pow,natDegree_X_sub_C,natDegree_X_sub_C] at hfull
      simpa using hfull.symm
    obtain ⟨T,U,u,v,hminTU,hTdeg,hUdeg,hu,hv,hrectT,hrectU,hprop⟩ :=
      degreeMinimal_two_root_subrectangular_pair R S hminRS lam α β a b
        hlam hab (by omega) (by omega) hdegree hcut
    exact ⟨T,U,a,b,u,v,hminTU,hTdeg.trans hRdeg,hUdeg.trans hSdeg,
      by omega,by omega,hu,hv,hrectT,hrectU,hprop⟩

theorem degreeMinimal_oriented_subrectangular_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ (R S : A1 ℂ) (a b u v : ℕ),
      IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < a ∧ a < b ∧ 0 < u ∧ 0 < v ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧ a*v=b*u := by
  obtain ⟨R,S,a,b,u,v,hminRS,hRdeg,hSdeg,ha,hb,hu,hv,hrectR,hrectS,hprop⟩ :=
    degreeMinimal_subrectangular_pair P Q hmin
  have hne := counterexample_subrectangular_corner_not_diagonal
    ggv_preliminary_companion_proved R S hminRS.1 a b hrectR (by omega)
  by_cases hab : a < b
  · exact ⟨R,S,a,b,u,v,hminRS,hRdeg,hSdeg,ha,hab,hu,hv,hrectR,hrectS,hprop⟩
  · exact ⟨fourierAlgHom ℂ R,fourierAlgHom ℂ S,b,a,v,u,
      degreeMinimal_fourier_preserved R S hminRS,
      (totalDeg_fourier_eq R).trans hRdeg,(totalDeg_fourier_eq S).trans hSdeg,
      hb,by omega,hv,hu,
      subrectangular_fourier_at R a b hrectR (by omega),
      subrectangular_fourier_at S u v hrectS (by omega),hprop.symm⟩

end Dixmier.Weyl
