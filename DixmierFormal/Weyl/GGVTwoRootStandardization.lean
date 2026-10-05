/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FourierDiagonalSymbol
public import DixmierFormal.Weyl.GGVSingleFactorStandardization

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Standardization of two distinct diagonal linear factors

A common linear shear and Fourier exchange turn two finite roots into
an axis factor and one finite root. A second linear shear gives occupied
proportional rectangles while retaining both total degrees and minimality.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem degreeMinimal_fourier_preserved (P Q : A1 ℂ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    IsDegreeMinimalCounterexamplePair (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) := by
  refine ⟨isCounterexamplePair_fourier P Q hmin.1, ?_⟩
  intro R S hRS
  rw [totalDeg_fourier_eq, totalDeg_fourier_eq]
  exact hmin.2 R S hRS

theorem degreeMinimal_two_root_subrectangular_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (lam α β : ℂ) (u v : ℕ) (hlam : lam ≠ 0) (hab : α ≠ β)
    (hu : 0 < u) (hv : 0 < v) (hdegree : totalDeg P.1 = u+v)
    (hcut : cutPoly 1 1 P.1 = Polynomial.C lam *
      (Polynomial.X-Polynomial.C α)^u * (Polynomial.X-Polynomial.C β)^v) :
    ∃ (R S : A1 ℂ) (a b : ℕ), IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < a ∧ 0 < b ∧ IsSubrectangularAt R u v ∧
      IsSubrectangularAt S a b ∧ u*b=v*a := by
  obtain ⟨R,S,hminRS,hRdeg,hSdeg,hRcut,_,_,_⟩ :=
    degreeMinimal_linear_cut_recovers_pair P Q α hmin
  let γ : ℂ := β-α
  have hγ : γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hcutR : cutPoly 1 1 R.1 = Polynomial.C lam * Polynomial.X^u *
      (Polynomial.X-Polynomial.C γ)^v := by
    rw [hRcut,hcut]
    simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,
      Polynomial.X_comp,Polynomial.C_comp]
    have he : Polynomial.X+Polynomial.C α-Polynomial.C β =
        Polynomial.X-Polynomial.C γ := by
      dsimp [γ]
      rw [map_sub]
      ring
    rw [add_sub_cancel_right,he]
  have hp := counterexample_vDeg_pos_all_directions R S hminRS.1 1 1
    (by norm_num [IsDirection])
  have hweight : vDeg 1 1 R.1 = ((0+u+v : ℕ) : ℤ) := by
    rw [← totalDeg_eq_vDeg_one_one R hp,hRdeg,hdegree]
    simp
  have hface := diagonal_face_eq_of_factored_cut R lam 0 γ 0 u v hweight
    (by simpa using hcutR)
  have hface' : leadingForm 1 1 R.1 = MvPolynomial.C lam *
      MvPolynomial.X 1^u *
      (MvPolynomial.X 1-MvPolynomial.C γ*MvPolynomial.X 0)^v := by
    simpa using hface
  let lam' : ℂ := lam * (-1)^u * (-γ)^v
  have hlam' : lam' ≠ 0 := mul_ne_zero (mul_ne_zero hlam
    (pow_ne_zero u (by norm_num))) (pow_ne_zero v (neg_ne_zero.mpr hγ))
  have hFcut : cutPoly 1 1 (fourierAlgHom ℂ R).1 = Polynomial.C lam' *
      (Polynomial.X-Polynomial.C (-γ⁻¹))^v := by
    unfold cutPoly
    rw [counterexample_fourier_diagonal_leadingForm R S hminRS.1,hface']
    let ψ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin 2 => if i=0 then (1 : ℂ[X]) else Polynomial.X)
    change ψ (diagonalFourierSymbol _) = _
    simp only [map_mul,map_pow,map_sub,diagonalFourierSymbol,
      MvPolynomial.aeval_C,MvPolynomial.aeval_X,MvPolynomial.algebraMap_eq,
      if_true,if_false,map_neg]
    dsimp [ψ]
    simp only [MvPolynomial.eval₂_neg,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
    simp only [ite_true,if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have he : (-1 : ℂ[X])-Polynomial.C γ*Polynomial.X =
        Polynomial.C (-γ)*(Polynomial.X-Polynomial.C (-γ⁻¹)) := by
      rw [mul_sub,← Polynomial.C_mul]
      simp [hγ]
      ring
    rw [he,mul_pow]
    dsimp [lam']
    simp only [map_mul,map_pow,map_neg,map_one]
    ring
  obtain ⟨T,U,a,b,hminTU,hTdeg,hUdeg,ha,hb,hrectT,hrectU,hprop⟩ :=
    degreeMinimal_single_factor_subrectangular_pair
      (fourierAlgHom ℂ R) (fourierAlgHom ℂ S)
      (degreeMinimal_fourier_preserved R S hminRS) lam' (-γ⁻¹) u v
      hlam' hu hv (by rw [totalDeg_fourier_eq,hRdeg,hdegree]) hFcut
  exact ⟨T,U,a,b,hminTU,
    hTdeg.trans ((totalDeg_fourier_eq R).trans hRdeg),
    hUdeg.trans ((totalDeg_fourier_eq S).trans hSdeg),
    ha,hb,hrectT,hrectU,hprop⟩

end Dixmier.Weyl
