/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalMate
public import DixmierFormal.Weyl.DescentTermination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal exact mate descent

At horizontal weight, the leading-face classification and exact Weyl
subtraction yield a terminating descent to a mate exponent not divisible
by the outer prime. The published opposite-grade input remains explicit.
-/

namespace Dixmier.Weyl

open MvPolynomial

set_option maxHeartbeats 1000000 in
/-- Exact horizontal mate subtraction terminates without a mate bound. -/
theorem horizontal_mate_descent_terminal
    (H : GGVInputs) (P Q : A1 ℂ) (μ α : ℂ)
    (p : ℕ) (hμ : μ ≠ 0) (hp : 2 ≤ p)
    (hPweight : vDeg 1 0 P.1 = (p : ℤ))
    (hPface : leadingForm 1 0 P.1 =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ p)
    (h : IsCounterexamplePair P Q) :
    ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
      IsCounterexamplePair P Q' ∧ 0 < j ∧ ¬ p ∣ j ∧ ν ≠ 0 ∧
      vDeg 1 0 Q'.1 = j ∧
      leadingForm 1 0 Q'.1 =
        MvPolynomial.C ν *
          (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
            MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j := by
  let measure (T : A1 ℂ) : ℕ :=
    (vDeg 1 0 T.1).toNat
  have step : ∀ (n : ℕ) (T : A1 ℂ), measure T = n →
      IsCounterexamplePair P T →
      ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
        IsCounterexamplePair P Q' ∧ 0 < j ∧ ¬ p ∣ j ∧ ν ≠ 0 ∧
        vDeg 1 0 Q'.1 = j ∧
        leadingForm 1 0 Q'.1 =
          MvPolynomial.C ν *
            (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
              MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hmeasure hT
      have hTpos : 0 < vDeg 1 0 T.1 :=
        counterexample_mate_weight_pos H P T hT 1 0 (by decide)
      have hTweight : vDeg 1 0 T.1 = (n : ℤ) := by
        dsimp [measure] at hmeasure
        omega
      obtain ⟨j, ν, hjpos, hν, hjweight, hTface⟩ :=
        horizontal_mate_is_base_power H P T α μ p hμ hp hPface hT
      by_cases hdiv : p ∣ j
      · obtain ⟨k, hk⟩ := hdiv
        have hkpos : 0 < k := by
          rcases k with _ | k
          · simp [hk] at hjpos
          · omega
        obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
        let c : ℂ := ν * (μ ^ (u + 1))⁻¹
        let T' : A1 ℂ := T - c • P ^ (u + 1)
        have hT' : IsCounterexamplePair P T' :=
          isCounterexamplePair_mateSubtraction P T c (u + 1) hT
        have hT'pos : 0 < vDeg 1 0 T'.1 :=
          counterexample_mate_weight_pos H P T' hT' 1 0 (by decide)
        have hPpos : 0 < vDeg 1 0 P.1 := by
          rw [hPweight]
          have hpz : 0 < (p : ℤ) := by exact_mod_cast (by omega : 0 < p)
          exact hpz
        have hPdeg := weightedDegree_eq_coe_of_vDeg_pos P 1 0 hPpos
        have hTdeg := weightedDegree_eq_coe_of_vDeg_pos T 1 0 hTpos
        have hTweight' : vDeg 1 0 T.1 =
            ((u + 1 : ℕ) : ℤ) * (p : ℤ) := by
          calc
            vDeg 1 0 T.1 = (n : ℤ) := hTweight
            _ = (j : ℤ) := by omega
            _ = ((u + 1 : ℕ) : ℤ) * (p : ℤ) := by
              rw [hk]
              push_cast
              ring
        have hpositive : 0 < ((u + 1 : ℕ) : ℤ) * (p : ℤ) := by
          rw [← hTweight']
          exact hTpos
        have hdirection : 0 < (1 : ℤ) + 0 := by decide
        have hdrop : vDeg 1 0 T'.1 <
            ((u + 1 : ℕ) : ℤ) * (p : ℤ) := by
          exact mateSubtraction_weight_drop_of_purePower_faces P T
            (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
              MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) μ ν hμ hν p u 1 0
            (p : ℤ) hdirection hpositive
            (by simpa only [hPweight] using hPdeg)
            (by rw [hTweight'] at hTdeg; exact hTdeg)
            hPface (by simpa only [hk] using hTface)
        have hdropn : measure T' < n := by
          have hlt : vDeg 1 0 T'.1 < (n : ℤ) := by
            rw [← hTweight', hTweight] at hdrop
            exact hdrop
          have hnonneg : 0 ≤ vDeg 1 0 T'.1 := le_of_lt hT'pos
          dsimp [measure]
          omega
        exact ih (measure T') hdropn T' rfl hT'
      · exact ⟨T, j, ν, hT, hjpos, hdiv, hν, hjweight, hTface⟩
  exact step (measure Q) Q rfl h

end Dixmier.Weyl
