/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeCornerExclusion
public import DixmierFormal.Weyl.GGVDegreeOnlyInputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Unconditional degree bound and mass-six generation -/
namespace Dixmier.Weyl

theorem degreeMinimal_degree_bound_proved
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1) := by
  by_contra h
  have hsmall : Nat.gcd (totalDeg P.1) (totalDeg Q.1) ≤ 15 := by omega
  obtain ⟨H⟩ := degreeMinimal_small_degree_crossing_data P Q hmin hsmall
  exact smallDegreeCrossing_impossible P Q H

theorem ggv_degree_bound_proved
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1) :=
  degreeBound_of_minimalPair_bound degreeMinimal_degree_bound_proved P Q hpair

/-- All six published structural inputs are discharged internally. -/
theorem ggvInputs_proved : GGVInputs :=
  ggvInputs_of_degree_bound ggv_degree_bound_proved

/-- The frozen mass-six statement, over every characteristic-zero field
and with no restriction on the mate, without a structural-input premise. -/
theorem massSixGeneration : Statement.MassSixGeneration :=
  massSixGeneration_of_degree_bound ggv_degree_bound_proved

end Dixmier.Weyl
