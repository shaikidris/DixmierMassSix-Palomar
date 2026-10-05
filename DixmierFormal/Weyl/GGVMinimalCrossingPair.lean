/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVMinimalStandardization
public import DixmierFormal.Weyl.GGVHorizontalMinimality

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual strict crossing from every degree-minimal pair

The occupied proportional rectangles are constructed internally. A common
horizontal cut retains their degrees and minimality, and the finite face
selection supplies one actual primitive direction shared by both operators.
-/
namespace Dixmier.Weyl

theorem degreeMinimal_negative_horizontal_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ (R S : A1 ℂ) (a b u v : ℕ),
      IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < a ∧ a < b ∧ 0 < u ∧ 0 < v ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧ a*v=b*u ∧
      (∀ e ∈ (leadingForm 1 0 R.1).support, grade e < 0) := by
  classical
  obtain ⟨T,U,a,b,u,v,hminTU,hTdeg,hUdeg,ha,hab,hu,hv,hrectT,hrectU,hprop⟩ :=
    degreeMinimal_oriented_subrectangular_pair P Q hmin
  by_cases hface : InDir 1 0 T.1
  · obtain ⟨R,S,hminRS,hrectR,hrectS,hterminal⟩ :=
      preliminary_degreeMinimal_horizontal_standardization
        ggv_preliminary_companion_proved T U a b u v hminTU hrectT hrectU hab hface
    have hRdeg : totalDeg R.1 = totalDeg T.1 :=
      (subrectangular_totalDeg_eq R a b hrectR).trans
        (subrectangular_totalDeg_eq T a b hrectT).symm
    have hSdeg : totalDeg S.1 = totalDeg U.1 :=
      (subrectangular_totalDeg_eq S u v hrectS).trans
        (subrectangular_totalDeg_eq U u v hrectU).symm
    exact ⟨R,S,a,b,u,v,hminRS,hRdeg.trans hTdeg,hSdeg.trans hUdeg,
      ha,hab,hu,hv,hrectR,hrectS,hprop,hterminal⟩
  · obtain ⟨w,hw,hwmin,hwneg⟩ :=
      subrectangular_horizontal_start_negative_of_no_dir T a b hrectT hab hface
    exact ⟨T,U,a,b,u,v,hminTU,hTdeg,hUdeg,ha,hab,hu,hv,hrectT,hrectU,hprop,
      horizontal_min_y_negative_all T w hw hwmin hwneg⟩

theorem degreeMinimal_strict_crossing_pair
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ∃ (R S : A1 ℂ) (a b u v : ℕ)
      (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes R).length)
      (ρ s : ℕ) (e f : Fin 2 →₀ ℕ),
      IsDegreeMinimalCounterexamplePair R S ∧
      totalDeg R.1 = totalDeg P.1 ∧ totalDeg S.1 = totalDeg Q.1 ∧
      0 < a ∧ a < b ∧ 0 < u ∧ 0 < v ∧
      IsSubrectangularAt R a b ∧ IsSubrectangularAt S u v ∧ a*v=b*u ∧
      (∀ x ∈ (leadingForm 1 0 R.1).support, grade x < 0) ∧
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes R)[j]'hj = (-(s : ℤ) : ℚ)/ρ ∧
      InDir (ρ : ℤ) (-(s : ℤ)) R.1 ∧ InDir (ρ : ℤ) (-(s : ℤ)) S.1 ∧
      e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) R.1).support ∧
      f ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) R.1).support ∧
      (∀ x ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) R.1).support, e 1 ≤ x 1) ∧
      (∀ x ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) R.1).support, x 1 ≤ f 1) ∧
      0 < grade e ∧ grade f < 0 := by
  obtain ⟨R,S,a,b,u,v,hminRS,hRdeg,hSdeg,ha,hab,hu,hv,hrectR,hrectS,hprop,hterminal⟩ :=
    degreeMinimal_negative_horizontal_pair P Q hmin
  obtain ⟨j,hj,ρ,s,e,f,hρ,hs,hdir,hentry,hfaceR,hfaceS,he,hf,hemin,hfmax,
      hepos,hfneg⟩ := counterexample_ordered_strict_crossing_of_terminal
    ggv_preliminary_companion_proved R S hminRS.1 hterminal
  exact ⟨R,S,a,b,u,v,j,hj,ρ,s,e,f,hminRS,hRdeg,hSdeg,ha,hab,hu,hv,
    hrectR,hrectS,hprop,hterminal,hρ,hs,hdir,hentry,hfaceR,hfaceS,
    he,hf,hemin,hfmax,hepos,hfneg⟩

end Dixmier.Weyl
