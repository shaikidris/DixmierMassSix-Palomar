/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Reduction of the global degree bound to a minimal counterexample pair

G13 Corollary 7.4 chooses a pair minimizing the gcd of its two total
degrees. This file isolates that well-ordering step. It does not assert
that a minimal pair is standard or prove the geometric lower bound.
-/

namespace Dixmier.Weyl

/-- A counterexample pair minimizing the gcd of its total degrees among
all counterexample pairs over `ℂ`. -/
def IsDegreeMinimalCounterexamplePair (P Q : A1 ℂ) : Prop :=
  IsCounterexamplePair P Q ∧
    ∀ R S : A1 ℂ, IsCounterexamplePair R S →
      Nat.gcd (totalDeg P.1) (totalDeg Q.1) ≤
        Nat.gcd (totalDeg R.1) (totalDeg S.1)

/-- If a counterexample exists, the well-ordering of natural numbers
provides a degree-gcd minimal one. -/
theorem exists_degreeMinimalCounterexamplePair
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    ∃ R S : A1 ℂ, IsDegreeMinimalCounterexamplePair R S := by
  let values : Set ℕ :=
    {d | ∃ R S : A1 ℂ,
      IsCounterexamplePair R S ∧ d = Nat.gcd (totalDeg R.1) (totalDeg S.1)}
  have hne : values.Nonempty := by
    refine ⟨Nat.gcd (totalDeg P.1) (totalDeg Q.1), P, Q, hpair, rfl⟩
  obtain ⟨d, hd, hleast⟩ := wellFounded_lt.has_min values hne
  obtain ⟨R, S, hRS, rfl⟩ := hd
  refine ⟨R, S, hRS, ?_⟩
  intro T U hTU
  exact Nat.le_of_not_gt (hleast _ ⟨T, U, hTU, rfl⟩)

/-- The source's minimal-pair lower bound implies the frozen global
degree-bound contract without changing the mate or imposing an order bound. -/
theorem degreeBound_of_minimalPair_bound
    (hminimal : ∀ P Q : A1 ℂ,
      IsDegreeMinimalCounterexamplePair P Q →
        15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1) := by
  intro P Q hpair
  obtain ⟨R, S, hmin⟩ := exists_degreeMinimalCounterexamplePair P Q hpair
  exact lt_of_lt_of_le (hminimal R S hmin) (hmin.2 P Q hpair)

end Dixmier.Weyl
