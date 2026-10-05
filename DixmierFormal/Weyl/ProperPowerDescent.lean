/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DescentTermination
public import DixmierFormal.Weyl.GGVPositiveWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The general mate-descent step in Han--Tan's proper-power argument

This isolates the well-founded argument from the two still-unproved source
inputs: the homogeneous Poisson centralizer of a non-power form, and the
generation theorem when the leading Poisson bracket is one. Neither input is
asserted as an axiom. The conclusion is deliberately a contradiction for a
counterexample with those two local properties, not the GGV proper-power field.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- If every zero-bracket mate face is a scalar power of the first face, and
the bracket-one alternative is excluded, positive mate-weight descent rules
out a counterexample. The power statement is made about every exact mate
obtained by subtraction, as required by the iteration. -/
theorem counterexample_impossible_of_power_face_descent
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hpair : IsCounterexamplePair P Q)
    (hone : ∀ T : A1 ℂ, IsCounterexamplePair P T →
      poisson (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) ≠ 1)
    (hzero : ∀ T : A1 ℂ, IsCounterexamplePair P T →
      poisson (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) = 0 →
      ∃ (c : ℂ) (n : ℕ), c ≠ 0 ∧
        vDeg ρ σ T.1 = ((n + 1 : ℕ) : ℤ) * vDeg ρ σ P.1 ∧
        leadingForm ρ σ T.1 = c • (leadingForm ρ σ P.1) ^ (n + 1)) :
    False := by
  let measure (T : A1 ℂ) : ℕ := (vDeg ρ σ T.1).toNat
  have step : ∀ n : ℕ, ∀ T : A1 ℂ,
      measure T = n → IsCounterexamplePair P T → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hmeasure hT
      have hPpos := counterexample_vDeg_pos_all_directions P T hT ρ σ hdir
      have hTpos := counterexample_vDeg_pos_all_directions T (-P)
        (isCounterexamplePair_swap_neg P T hT) ρ σ hdir
      rcases exactPair_leadingPoisson_zero_or_one P T ρ σ hdir.2 hT.1 with hz | ho
      · obtain ⟨c, k, hc, hweight, hface⟩ := hzero T hT hz
        let T' : A1 ℂ := T - c • P ^ (k + 1)
        have hT' : IsCounterexamplePair P T' :=
          isCounterexamplePair_mateSubtraction P T c (k + 1) hT
        have hT'pos := counterexample_vDeg_pos_all_directions T' (-P)
          (isCounterexamplePair_swap_neg P T' hT') ρ σ hdir
        have hPdeg := weightedDegree_eq_coe_of_vDeg_pos P ρ σ hPpos
        have hTdeg := weightedDegree_eq_coe_of_vDeg_pos T ρ σ hTpos
        have hpositive : 0 < ((k + 1 : ℕ) : ℤ) * vDeg ρ σ P.1 := by
          rw [← hweight]
          exact hTpos
        have hdrop := mateSubtraction_weight_drop_of_power_face P T c hc k ρ σ
          (vDeg ρ σ P.1) hdir.2 hpositive hPdeg
          (by rw [hweight] at hTdeg; exact hTdeg) hface
        have hmeasureDrop : measure T' < n := by
          change (vDeg ρ σ T'.1).toNat < n
          have hn : (vDeg ρ σ T.1).toNat = n := hmeasure
          rw [← hweight] at hdrop
          change vDeg ρ σ T'.1 < vDeg ρ σ T.1 at hdrop
          omega
        exact ih (measure T') hmeasureDrop T' rfl hT'
      · exact hone T hT ho
  exact step (measure Q) Q rfl hpair

end Dixmier.Weyl
