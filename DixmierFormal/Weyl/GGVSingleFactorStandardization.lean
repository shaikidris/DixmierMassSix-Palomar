/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVLinearShearMinimality
public import DixmierFormal.Weyl.PositiveShearFiniteDescent
public import DixmierFormal.Weyl.GGVCompanionJosephFrontier
public import DixmierFormal.Weyl.GGVFourierRectangle

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Standardization of a diagonal face with an axis factor

A nonzero axis factor and a nonconstant linear factor give an occupied
rectangle after one exact linear shear. The unrestricted mate has an
occupied rectangle on the same ray, and the degree-minimal pair is retained.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem degreeMinimal_single_factor_subrectangular_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (lam α : ℂ) (a k : ℕ) (hlam : lam ≠ 0) (ha : 0 < a) (hk : 0 < k)
    (hdegree : totalDeg P.1 = a+k)
    (hcut : cutPoly 1 1 P.1 = Polynomial.C lam * (Polynomial.X-Polynomial.C α)^k) :
    ∃ (R S : A1 ℂ) (u v : ℕ), IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < u ∧ 0 < v ∧ IsSubrectangularAt R a k ∧
      IsSubrectangularAt S u v ∧ a*v=k*u := by
  obtain ⟨R,S,hminRS,hRdeg,hSdeg,hRcut,_,_,_⟩ :=
    degreeMinimal_linear_cut_recovers_pair P Q α hmin
  have hcutR : cutPoly 1 1 R.1 = Polynomial.C lam * Polynomial.X^k := by
    rw [hRcut,hcut]
    simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,
      Polynomial.X_comp,Polynomial.C_comp]
    simp
  have hp := counterexample_vDeg_pos_all_directions R S hminRS.1 1 1
    (by norm_num [IsDirection])
  have hRtotal : totalDeg R.1 = a+k := hRdeg.trans hdegree
  have hRweight : vDeg 1 1 R.1 = ((a+k+0 : ℕ) : ℤ) := by
    rw [← totalDeg_eq_vDeg_one_one R hp,hRtotal]
    simp
  have hf := diagonal_face_eq_of_factored_cut R lam 0 0 a k 0 hRweight
    (by simpa using hcutR)
  have hf' : leadingForm 1 1 R.1 =
      MvPolynomial.C lam * MvPolynomial.X 0^a * MvPolynomial.X 1^k := by
    simpa using hf
  have hsupport : (leadingForm 1 1 R.1).support = {expo a k} := by
    rw [hf']
    exact weighted_monomial_support lam hlam a k
  obtain ⟨u,v,hu,hv,hrectR,hrectS,hprop⟩ :=
    preliminary_companion_singleton_diagonal_pair_subrectangular
      ggv_preliminary_companion_proved R S hminRS.1 a k hRtotal
      (by simp [hsupport])
      (by intro e he; simpa [hsupport] using he) ha hk
  exact ⟨R,S,u,v,hminRS,hRdeg,hSdeg,hu,hv,hrectR,hrectS,hprop⟩

end Dixmier.Weyl
