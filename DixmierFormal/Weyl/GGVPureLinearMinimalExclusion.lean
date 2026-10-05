/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPositiveFaceMinimalExclusion
public import DixmierFormal.Weyl.GGVTwoRootStandardization

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Pure linear diagonal powers cannot be degree minimal

An exact linear shear removes the root and preserves both total degrees.
Fourier exchange turns the resulting pure Y face into a pure X face,
which is excluded by the positive-face degree descent.
-/
namespace Dixmier.Weyl
open Polynomial

theorem degreeMinimal_diagonal_y_power_impossible
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (lam : ℂ) (b : ℕ) (hlam : lam ≠ 0)
    (hf : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1 ^ b) :
    False := by
  classical
  have hmono : leadingForm 1 1 P.1 = MvPolynomial.monomial (expo 0 b) lam := by
    rw [hf,MvPolynomial.C_mul_X_pow_eq_monomial]
    simp [expo]
  have hF : leadingForm 1 1 (fourierAlgHom ℂ P).1 =
      MvPolynomial.C ((-1 : ℂ)^b * lam) * MvPolynomial.X 0 ^ b := by
    rw [counterexample_fourier_diagonal_leadingForm P Q hmin.1,hmono,
      diagonalFourierSymbol_monomial]
    simp only [MvPolynomial.smul_eq_C_mul,MvPolynomial.C_mul_monomial,
      MvPolynomial.C_mul_X_pow_eq_monomial]
    simp [expo]
  have hlam' : (-1 : ℂ)^b * lam ≠ 0 :=
    mul_ne_zero (pow_ne_zero b (by norm_num)) hlam
  have hsupport : (leadingForm 1 1 (fourierAlgHom ℂ P).1).support = {expo b 0} := by
    rw [hF]
    simpa using weighted_monomial_support ((-1 : ℂ)^b * lam) hlam' b 0
  exact degreeMinimal_diagonal_axis_singleton_impossible
    (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q)
    (degreeMinimal_fourier_preserved P Q hmin) b (by rw [hsupport]; simp)
    (by intro e he; simpa [hsupport] using he)

theorem degreeMinimal_pure_linear_diagonal_impossible
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (lam α : ℂ) (b : ℕ) (hlam : lam ≠ 0)
    (hdegree : totalDeg P.1 = b)
    (hc : cutPoly 1 1 P.1 = C lam * (X-C α)^b) : False := by
  obtain ⟨R,S,hminRS,hRdeg,_,hRcut,_,_,_⟩ :=
    degreeMinimal_linear_cut_recovers_pair P Q α hmin
  have hcut : cutPoly 1 1 R.1 = C lam * X^b := by
    rw [hRcut,hc]
    simp only [mul_comp,pow_comp,sub_comp,X_comp,C_comp]
    simp
  have hp := counterexample_vDeg_pos_all_directions R S hminRS.1 1 1
    (by norm_num [IsDirection])
  have hw : vDeg 1 1 R.1 = ((0+1*b : ℕ) : ℤ) := by
    rw [← totalDeg_eq_vDeg_one_one R hp,hRdeg,hdegree]
    simp
  have hf := positive_face_eq_of_linear_power_cut R lam 0 1 0 b hw
    (by simpa using hcut)
  exact degreeMinimal_diagonal_y_power_impossible R S hminRS lam b hlam
    (by simpa using hf)

end Dixmier.Weyl
