/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Inputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Han–Tan one-sided grade interface for the GGV opposite-grades input

The adapter below states the exact support-sign consequence used by `GGVInputs` from a
source-shaped version of Han–Tan's one-member theorem. The premise is an explicit proposition,
not an axiom. Its unconditional proof and the resulting `grades_opposite` field are supplied in
`OneSidedScalarNormalize.lean`.
-/

namespace Dixmier.Weyl

open MvPolynomial

def HanTanOneSidedGrades : Prop :=
  ∀ P Q : A1 ℂ, Q * P - P * Q = 1 →
    ((∀ d ∈ (symbol P.1).support, 0 ≤ grade d) ∨
     (∀ d ∈ (symbol P.1).support, grade d ≤ 0)) →
    Algebra.adjoin ℂ {P, Q} = ⊤

theorem grades_opposite_of_HanTan (hHT : HanTanOneSidedGrades) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      (∃ d ∈ (symbol P.1).support, 0 < grade d) ∧
      (∃ d ∈ (symbol P.1).support, grade d < 0) := by
  intro P Q hpair
  constructor
  · by_contra hn
    have hall : ∀ d ∈ (symbol P.1).support, grade d ≤ 0 := by
      intro d hd
      by_contra hnot
      exact hn ⟨d, hd, lt_of_not_ge hnot⟩
    exact hpair.2 (hHT P Q hpair.1 (Or.inr hall))
  · by_contra hn
    have hall : ∀ d ∈ (symbol P.1).support, 0 ≤ grade d := by
      intro d hd
      by_contra hnot
      exact hn ⟨d, hd, lt_of_not_ge hnot⟩
    exact hpair.2 (hHT P Q hpair.1 (Or.inl hall))

end Dixmier.Weyl
