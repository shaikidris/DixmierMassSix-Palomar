/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.MatePower
public import DixmierFormal.Weyl.Inputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positivity invariant for exact mate descent

Each mate subtraction keeps a counterexample pair. To iterate the strict
weighted-degree drop, the new mate must retain positive weight. The published
opposite-grade input supplies a positive grade for the mate after swapping the
pair and negating its first member; positive grade implies positive crossing
weight in a direction `(ρ,-s)` with `s < ρ`.
-/

namespace Dixmier.Weyl

open MvPolynomial

set_option maxHeartbeats 1000000 in
/-- Swapping an exact pair and negating its former first member preserves
the commutator convention `[Q,P]=1` and its generated algebra. -/
theorem isCounterexamplePair_swap_neg (P Q : A1 ℂ)
    (h : IsCounterexamplePair P Q) :
    IsCounterexamplePair Q (-P) := by
  have hadjoin : Algebra.adjoin ℂ ({Q, -P} : Set (A1 ℂ)) =
      Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) := by
    let S := Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ))
    let T := Algebra.adjoin ℂ ({Q, -P} : Set (A1 ℂ))
    have hPS : P ∈ S := Algebra.subset_adjoin (by simp)
    have hQS : Q ∈ S := Algebra.subset_adjoin (by simp)
    have hQT : Q ∈ T := Algebra.subset_adjoin (by simp)
    have hnPT : -P ∈ T := Algebra.subset_adjoin (by simp)
    have hnPS : -P ∈ S := by
      have hsmul := S.smul_mem hPS (-1 : ℂ)
      rw [neg_one_smul ℂ P] at hsmul
      exact hsmul
    have hPT : P ∈ T := by
      have hsmul := T.smul_mem hnPT (-1 : ℂ)
      rw [neg_one_smul ℂ (-P)] at hsmul
      have hdouble : -(-P) = P := neg_neg P
      rw [hdouble] at hsmul
      exact hsmul
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      change x ∈ S
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · simpa only [hx] using hQS
      · simpa only [hx] using hnPS
    · apply Algebra.adjoin_le
      intro x hx
      change x ∈ T
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · simpa only [hx] using hPT
      · simpa only [hx] using hQT
  constructor
  · calc
      (-P) * Q - Q * (-P) = Q * P - P * Q := by
        apply Subtype.ext
        simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg]
        apply LinearMap.ext
        intro x
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply]
        simp only [map_neg]
        abel
      _ = 1 := h.1
  · rw [hadjoin]
    exact h.2

/-- A positive grade in a polynomial support has positive `(ρ,-s)` weight
when `s < ρ`. This is the sign calculation used after every mate step. -/
theorem vDeg_pos_of_positive_grade
    (T : A1 ℂ) (ρ s : ℕ) (hsρ : s < ρ)
    (hgrade : ∃ d ∈ (symbol T.1).support, 0 < grade d) :
    0 < vDeg ρ (-(s : ℤ)) T.1 := by
  obtain ⟨d, hd, hgd⟩ := hgrade
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hposij : 0 < (i : ℤ) - j := by simpa [grade, expo] using hgd
  have hρ : 0 < (ρ : ℤ) := by exact_mod_cast (Nat.zero_lt_of_lt hsρ)
  have hsρz : (s : ℤ) < ρ := by exact_mod_cast hsρ
  have hgap : 0 ≤ (ρ : ℤ) - s := by omega
  have hfirst : 0 < ((i : ℤ) - j) * ρ := mul_pos hposij hρ
  have hsecond : 0 ≤ (j : ℤ) * ((ρ : ℤ) - s) :=
    mul_nonneg (by exact_mod_cast Nat.zero_le j) hgap
  have hw : 0 < Finsupp.weight (wt ρ (-(s : ℤ))) (expo i j) := by
    rw [expo_weight]
    nlinarith
  have hle : (Finsupp.weight (wt ρ (-(s : ℤ))) (expo i j) : WithBot ℤ) ≤
      weightedTotalDegree' (wt ρ (-(s : ℤ))) (symbol T.1) := by
    change (Finsupp.weight (wt ρ (-(s : ℤ))) (expo i j) : WithBot ℤ) ≤
      (symbol T.1).support.sup
        (fun e => (Finsupp.weight (wt ρ (-(s : ℤ))) e : WithBot ℤ))
    exact Finset.le_sup (f := fun e =>
      (Finsupp.weight (wt ρ (-(s : ℤ))) e : WithBot ℤ)) hd
  have htop : (0 : WithBot ℤ) <
      weightedTotalDegree' (wt ρ (-(s : ℤ))) (symbol T.1) :=
    lt_of_lt_of_le (WithBot.coe_lt_coe.mpr hw) hle
  change 0 < WithBot.unbotD 0
    (weightedTotalDegree' (wt ρ (-(s : ℤ))) (symbol T.1))
  cases hdeg : weightedTotalDegree' (wt ρ (-(s : ℤ))) (symbol T.1) with
  | bot => simp [hdeg] at htop
  | coe m =>
      simpa [hdeg] using htop

/-- Under the published opposite-grade hypothesis, every mate of a
counterexample pair has positive crossing weight, including after any exact
mate subtraction. -/
theorem counterexample_mate_weight_pos
    (H : GGVInputs) (P Q : A1 ℂ) (h : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hsρ : s < ρ) :
    0 < vDeg ρ (-(s : ℤ)) Q.1 := by
  have hswap := isCounterexamplePair_swap_neg P Q h
  exact vDeg_pos_of_positive_grade Q ρ s hsρ
    (GGVInputs.grades_opposite H Q (-P) hswap).1

/-- A strictly positive weighted degree is the actual (non-bottom) degree of
the finite PBW symbol. -/
theorem weightedDegree_eq_coe_of_vDeg_pos
    (T : A1 ℂ) (ρ σ : ℤ)
    (hpos : 0 < vDeg ρ σ T.1) :
    weightedTotalDegree' (wt ρ σ) (symbol T.1) =
      (vDeg ρ σ T.1 : WithBot ℤ) := by
  have hform : leadingForm ρ σ T.1 ≠ 0 :=
    leadingForm_ne_zero_of_vDeg_pos T ρ σ hpos
  have hsymbol : symbol T.1 ≠ 0 := by
    intro hz
    apply hform
    simp [leadingForm, hz]
  have hnotbot : weightedTotalDegree' (wt ρ σ) (symbol T.1) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  rw [← hm]
  simp [vDeg, ← hm]

set_option maxHeartbeats 1000000

/-- Exact mate subtraction terminates at a leading exponent not divisible by
`p`. This is conditional only on the published opposite-grade input, used to
keep each intermediate mate's weight positive. -/
theorem crossingFace_mate_descent_terminal
    (H : GGVInputs) (P Q : A1 ℂ) (μ α : ℂ)
    (p q ρ s : ℕ) (hμ : μ ≠ 0) (hp : 2 ≤ p)
    (hs : 0 < s) (hsρ : s < ρ)
    (hPweight : vDeg ρ (-(s : ℤ)) P.1 = (p : ℤ) * ρ)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (h : IsCounterexamplePair P Q) :
    ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
      IsCounterexamplePair P Q' ∧ 0 < j ∧ ¬ p ∣ j ∧ ν ≠ 0 ∧
      vDeg ρ (-(s : ℤ)) Q'.1 = (ρ * j : ℕ) ∧
      leadingForm ρ (-(s : ℤ)) Q'.1 =
        MvPolynomial.C ν *
          (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ j := by
  let measure (T : A1 ℂ) : ℕ :=
    (vDeg ρ (-(s : ℤ)) T.1).toNat
  have step : ∀ (n : ℕ) (T : A1 ℂ), measure T = n →
      IsCounterexamplePair P T →
      ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
        IsCounterexamplePair P Q' ∧ 0 < j ∧ ¬ p ∣ j ∧ ν ≠ 0 ∧
        vDeg ρ (-(s : ℤ)) Q'.1 = (ρ * j : ℕ) ∧
        leadingForm ρ (-(s : ℤ)) Q'.1 =
          MvPolynomial.C ν *
            (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) ^ j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hmeasure hT
      have hTpos : 0 < vDeg ρ (-(s : ℤ)) T.1 :=
        counterexample_mate_weight_pos H P T hT ρ s hsρ
      have hTweight : vDeg ρ (-(s : ℤ)) T.1 = (n : ℤ) := by
        dsimp [measure] at hmeasure
        omega
      obtain ⟨j, ν, hjpos, hν, hjweight, hTface⟩ :=
        crossingFace_mate_is_base_power P T μ α p q ρ s n hμ hp hs hsρ
          (by exact_mod_cast (show 0 < n by omega)) hT.1 hPweight hTweight hPface
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
        have hT'pos : 0 < vDeg ρ (-(s : ℤ)) T'.1 :=
          counterexample_mate_weight_pos H P T' hT' ρ s hsρ
        have hPpos : 0 < vDeg ρ (-(s : ℤ)) P.1 := by
          rw [hPweight]
          have hpz : 0 < (p : ℤ) := by exact_mod_cast (by omega : 0 < p)
          have hρz : 0 < (ρ : ℤ) := by exact_mod_cast (Nat.zero_lt_of_lt hsρ)
          exact mul_pos hpz hρz
        have hPdeg := weightedDegree_eq_coe_of_vDeg_pos P ρ (-(s : ℤ)) hPpos
        have hTdeg := weightedDegree_eq_coe_of_vDeg_pos T ρ (-(s : ℤ)) hTpos
        have hTweight' : vDeg ρ (-(s : ℤ)) T.1 =
            ((u + 1 : ℕ) : ℤ) * ((p : ℤ) * ρ) := by
          calc
            vDeg ρ (-(s : ℤ)) T.1 = (n : ℤ) := hTweight
            _ = ((ρ * j : ℕ) : ℤ) := by exact_mod_cast hjweight
            _ = ((u + 1 : ℕ) : ℤ) * ((p : ℤ) * ρ) := by
              rw [hk]
              push_cast
              ring
        have hpositive : 0 < ((u + 1 : ℕ) : ℤ) * ((p : ℤ) * ρ) := by
          rw [← hTweight']
          exact hTpos
        have hdirection : 0 < (ρ : ℤ) + -(s : ℤ) := by omega
        have hdrop : vDeg ρ (-(s : ℤ)) T'.1 <
            ((u + 1 : ℕ) : ℤ) * ((p : ℤ) * ρ) := by
          exact mateSubtraction_weight_drop_of_purePower_faces P T
            (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) μ ν hμ hν p u ρ (-(s : ℤ))
            ((p : ℤ) * ρ) hdirection hpositive
            (by simpa only [hPweight] using hPdeg)
            (by rw [hTweight'] at hTdeg; exact hTdeg)
            hPface (by simpa only [hk] using hTface)
        have hdropn : measure T' < n := by
          have hlt : vDeg ρ (-(s : ℤ)) T'.1 < (n : ℤ) := by
            rw [← hTweight', hTweight] at hdrop
            exact hdrop
          have hnonneg : 0 ≤ vDeg ρ (-(s : ℤ)) T'.1 := le_of_lt hT'pos
          dsimp [measure]
          omega
        exact ih (measure T') hdropn T' rfl hT'
      · exact ⟨T, j, ν, hT, hjpos, hdiv, hν, by
          rw [hTweight, hjweight]
          , hTface⟩
  exact step (measure Q) Q rfl h

end Dixmier.Weyl
