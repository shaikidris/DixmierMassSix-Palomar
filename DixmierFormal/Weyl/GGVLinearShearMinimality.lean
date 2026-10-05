/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVMinimalDegreeNondivisibility
public import DixmierFormal.Weyl.PolynomialCutTranslation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Degree minimality under a linear polynomial shear

The substitution fixing X and sending Y to Y+cX preserves total degree
and translates the diagonal cut polynomial. Applying it to both members
of an exact polynomial pair preserves their degree-gcd minimality.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

/-- A recovered linear cut preserves total degree and the full diagonal
cut polynomial of any two positive-degree operators. -/
theorem polynomial_linear_cut_totalDeg_and_translate
    (P R : A1 ℂ) (c : ℂ) (hPne : P ≠ 0)
    (hp : 0 < vDeg 1 1 P.1) (hr : 0 < vDeg 1 1 R.1)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 1 c (polynomialRamifiedLift 1 P)) :
    totalDeg R.1 = totalDeg P.1 ∧
      cutPoly 1 1 R.1 = (cutPoly 1 1 P.1).comp (Polynomial.X+Polynomial.C c) := by
  have ht := polynomial_monomial_cut_weight_and_translate P R 1 c hPne hp hr hrecover
  refine ⟨?_, ht.2⟩
  have hdP := totalDeg_eq_vDeg_one_one P hp
  have hdR := totalDeg_eq_vDeg_one_one R hr
  have heq : (totalDeg R.1 : ℤ) = totalDeg P.1 := hdR.trans (ht.1.trans hdP.symm)
  exact_mod_cast heq

/-- The common linear shear produces an actual degree-minimal polynomial
pair with unchanged two total degrees and translated diagonal cut faces. -/
theorem degreeMinimal_linear_cut_recovers_pair
    (P Q : A1 ℂ) (c : ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      cutPoly 1 1 R.1 = (cutPoly 1 1 P.1).comp (Polynomial.X+Polynomial.C c) ∧
      cutPoly 1 1 S.1 = (cutPoly 1 1 Q.1).comp (Polynomial.X+Polynomial.C c) ∧
      polynomialRamifiedLift 1 R =
        ramifiedCutAut 1 (by norm_num) 1 1 c (polynomialRamifiedLift 1 P) ∧
      polynomialRamifiedLift 1 S =
        ramifiedCutAut 1 (by norm_num) 1 1 c (polynomialRamifiedLift 1 Q) := by
  obtain ⟨R,S,hRS,hR,hS⟩ :=
    polynomial_monomial_cut_recovers_polynomial_counterexample 1 c P Q hmin.1
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hp := counterexample_vDeg_pos_all_directions P Q hmin.1 1 1 hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hmin.1) 1 1 hdir
  have hr := counterexample_vDeg_pos_all_directions R S hRS 1 1 hdir
  have hs := counterexample_vDeg_pos_all_directions S (-R)
    (isCounterexamplePair_swap_neg R S hRS) 1 1 hdir
  have hPne : P ≠ 0 := by
    intro hz
    have h := congrArg Subtype.val hmin.1.1
    rw [hz] at h
    simp at h
  have hQne : Q ≠ 0 := by
    intro hz
    have h := congrArg Subtype.val hmin.1.1
    rw [hz] at h
    simp at h
  have hRt := polynomial_linear_cut_totalDeg_and_translate P R c hPne hp hr hR
  have hSt := polynomial_linear_cut_totalDeg_and_translate Q S c hQne hq hs hS
  refine ⟨R,S,⟨hRS,?_⟩,hRt.1,hSt.1,hRt.2,hSt.2,hR,hS⟩
  intro T U hTU
  rw [hRt.1,hSt.1]
  exact hmin.2 T U hTU

end Dixmier.Weyl
