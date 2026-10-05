/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedFaceDispatch
public import DixmierFormal.Weyl.NoProperPowerMate
public import DixmierFormal.Weyl.AffineExactPair
public import Mathlib.Data.Int.Lemmas

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Bracket-one exclusion on negative and horizontal crossing directions

A counterexample member has an occupied positive-grade PBW point.
When `ρ > 0`, `σ ≤ 0`, and `ρ+σ > 0`, that point has weight at least
`ρ`. If the leading Poisson bracket of an exact pair were one, its two
positive leading weights would sum to `ρ+σ ≤ ρ`, a contradiction.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem positive_grade_weight_ge_rho
    (ρ σ : ℤ) (a : Fin 2 →₀ ℕ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (hgrade : 0 < grade a) :
    ρ ≤ Finsupp.weight (wt ρ σ) a := by
  have hgap : 1 ≤ (a 0 : ℤ) - a 1 := by
    simp [grade] at hgrade
    omega
  have hrest : 0 ≤ (ρ + σ) * (a 1 : ℤ) :=
    mul_nonneg (le_of_lt hsum) (by positivity)
  have hweight : Finsupp.weight (wt ρ σ) a =
      ρ * ((a 0 : ℤ) - a 1) + (ρ + σ) * (a 1 : ℤ) := by
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, wt]
    ring
  rw [hweight]
  nlinarith

theorem counterexample_vDeg_ge_rho_of_positive_grade
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ + σ) :
    ρ ≤ vDeg ρ σ P.1 := by
  obtain ⟨a, ha, hgrade⟩ := (ggv_grades_opposite_proved P Q hpair).1
  have hweight := positive_grade_weight_ge_rho ρ σ a hρ hsum hgrade
  have hleBot : (Finsupp.weight (wt ρ σ) a : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) := by
    rw [MvPolynomial.weightedTotalDegree']
    exact Finset.le_sup
      (f := fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) ha
  have hsymbol : symbol P.1 ≠ 0 := by
    intro hz
    have hsupport : (symbol P.1).support = ∅ := by simp [hz]
    rw [hsupport] at ha
    exact Finset.notMem_empty a ha
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  have hwd : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) =
      (vDeg ρ σ P.1 : WithBot ℤ) := by
    rw [← hm]
    simp [vDeg, ← hm]
  rw [hwd] at hleBot
  exact le_trans hweight (WithBot.coe_le_coe.mp hleBot)

theorem bracket_one_impossible_of_nonpositive_sigma
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 1 := by
  intro hbr
  have hP : ρ ≤ vDeg ρ σ P.1 :=
    counterexample_vDeg_ge_rho_of_positive_grade P Q hpair ρ σ hρ hdir.2
  have hQ : 0 < vDeg ρ σ Q.1 :=
    counterexample_vDeg_pos_all_directions Q (-P)
      (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hsum := leading_weights_sum_of_bracket_one P Q ρ σ hdir hpair hbr
  omega

/-- A direction-local bracket-one exclusion gives the exact homogeneous
proper-power face, including the unrestricted mate descent. -/
theorem ggv_proper_power_of_local_bracket_one_exclusion
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hone : ∀ T : A1 ℂ, IsCounterexamplePair P T →
      poisson (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) ≠ 1) :
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k := by
  obtain ⟨d, S, μ, hd, hμ, hface⟩ :=
    counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion
      P Q ρ σ hdir hpair hone
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hPne := leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : d ≠ 0), mul_zero] at hface
    exact hPne hface
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hSpowhom : (S ^ d).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) := by
    intro a ha
    apply hPhom
    have hmem : a ∈ (S ^ d).support := mem_support_iff.mpr ha
    have hscaled : a ∈ (MvPolynomial.C μ * S ^ d).support := by
      rw [MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
      exact hmem
    exact mem_support_iff.mp (hface ▸ hscaled)
  obtain ⟨m, hShom, hm⟩ :=
    weighted_homogeneous_root_of_power S ρ σ (vDeg ρ σ P.1) d hS
      (by omega) hSpowhom
  exact ⟨μ, d, S, m, hμ, hd, hS, hShom, hface⟩

/-- The exact GGV proper-power face holds unconditionally for every
negative or horizontal crossing direction. The mate has no order or
mass bound. -/
theorem ggv_proper_power_nonpositive_sigma
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) :
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k := by
  apply ggv_proper_power_of_local_bracket_one_exclusion
    P Q hpair ρ σ hdir
  intro T hT
  exact bracket_one_impossible_of_nonpositive_sigma P T hT ρ σ hdir hρ hσ

/-- The symmetric support inequality uses the negative-grade point of
the same counterexample member. -/
theorem negative_grade_weight_ge_sigma
    (ρ σ : ℤ) (a : Fin 2 →₀ ℕ)
    (hσ : 0 < σ) (hsum : 0 < ρ + σ)
    (hgrade : grade a < 0) :
    σ ≤ Finsupp.weight (wt ρ σ) a := by
  have hgap : 1 ≤ (a 1 : ℤ) - a 0 := by
    simp [grade] at hgrade
    omega
  have hrest : 0 ≤ (ρ + σ) * (a 0 : ℤ) :=
    mul_nonneg (le_of_lt hsum) (by positivity)
  have hweight : Finsupp.weight (wt ρ σ) a =
      σ * ((a 1 : ℤ) - a 0) + (ρ + σ) * (a 0 : ℤ) := by
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, wt]
    ring
  rw [hweight]
  nlinarith

theorem counterexample_vDeg_ge_sigma_of_negative_grade
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hσ : 0 < σ) (hsum : 0 < ρ + σ) :
    σ ≤ vDeg ρ σ P.1 := by
  obtain ⟨a, ha, hgrade⟩ := (ggv_grades_opposite_proved P Q hpair).2
  have hweight := negative_grade_weight_ge_sigma ρ σ a hσ hsum hgrade
  have hleBot : (Finsupp.weight (wt ρ σ) a : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) := by
    rw [MvPolynomial.weightedTotalDegree']
    exact Finset.le_sup
      (f := fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) ha
  have hsymbol : symbol P.1 ≠ 0 := by
    intro hz
    have hsupport : (symbol P.1).support = ∅ := by simp [hz]
    rw [hsupport] at ha
    exact Finset.notMem_empty a ha
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  have hwd : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) =
      (vDeg ρ σ P.1 : WithBot ℤ) := by
    rw [← hm]
    simp [vDeg, ← hm]
  rw [hwd] at hleBot
  exact le_trans hweight (WithBot.coe_le_coe.mp hleBot)

theorem bracket_one_impossible_of_nonpositive_rho
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : ρ ≤ 0) (hσ : 0 < σ) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 1 := by
  intro hbr
  have hP : σ ≤ vDeg ρ σ P.1 :=
    counterexample_vDeg_ge_sigma_of_negative_grade P Q hpair ρ σ hσ hdir.2
  have hQ : 0 < vDeg ρ σ Q.1 :=
    counterexample_vDeg_pos_all_directions Q (-P)
      (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hsum := leading_weights_sum_of_bracket_one P Q ρ σ hdir hpair hbr
  omega

/-- The homogeneous proper-power face also holds on the reflected
nonpositive-first-coordinate sector. -/
theorem ggv_proper_power_nonpositive_rho
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : ρ ≤ 0) (hσ : 0 < σ) :
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k := by
  apply ggv_proper_power_of_local_bracket_one_exclusion
    P Q hpair ρ σ hdir
  intro T hT
  exact bracket_one_impossible_of_nonpositive_rho P T hT ρ σ hdir hρ hσ

/-- The proper-power half of GGV Proposition 2.6 is now unconditional
outside the strictly positive quadrant of primitive directions. -/
theorem ggv_proper_power_outside_positive_quadrant
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hsector : ρ ≤ 0 ∨ σ ≤ 0) :
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k := by
  have hsum := hdir.2
  rcases hsector with hρ | hσ
  · exact ggv_proper_power_nonpositive_rho P Q hpair ρ σ hdir hρ (by omega)
  · exact ggv_proper_power_nonpositive_sigma P Q hpair ρ σ hdir (by omega) hσ

/-- In the positive quadrant, opposite grades for both counterexample
members force each leading weight above both coordinate weights. The
only arithmetic equality case is the diagonal `(1,1)`, already excluded
by affine generation. -/
theorem bracket_one_impossible_positive_quadrant
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 1 := by
  intro hbr
  have hswap := isCounterexamplePair_swap_neg P Q hpair
  have hPρ := counterexample_vDeg_ge_rho_of_positive_grade
    P Q hpair ρ σ hρ hdir.2
  have hPσ := counterexample_vDeg_ge_sigma_of_negative_grade
    P Q hpair ρ σ hσ hdir.2
  have hQρ := counterexample_vDeg_ge_rho_of_positive_grade
    Q (-P) hswap ρ σ hρ hdir.2
  have hQσ := counterexample_vDeg_ge_sigma_of_negative_grade
    Q (-P) hswap ρ σ hσ hdir.2
  have hsum := leading_weights_sum_of_bracket_one P Q ρ σ hdir hpair hbr
  have heq : ρ = σ := by omega
  subst σ
  have hnat : ρ.natAbs = 1 := by
    simpa [IsDirection, Int.gcd] using hdir.1
  have hsq : ρ ^ 2 = 1 := by
    have habs : ρ.natAbs = (1 : ℤ).natAbs := by simpa using hnat
    simpa using (Int.natAbs_eq_iff_sq_eq.mp habs)
  have hρone : ρ = 1 := by nlinarith
  subst ρ
  exact bracket_one_diagonal_impossible P Q hpair hbr

/-- The bracket-one alternative is impossible for every primitive
positive-sum direction of a counterexample pair. -/
theorem ggv_bracket_one_input_proved : GGVBracketOneInput := by
  intro P Q hpair ρ σ hdir
  by_cases hρ : ρ ≤ 0
  · exact bracket_one_impossible_of_nonpositive_rho
      P Q hpair ρ σ hdir hρ (by have := hdir.2; omega)
  by_cases hσ : σ ≤ 0
  · exact bracket_one_impossible_of_nonpositive_sigma
      P Q hpair ρ σ hdir (by omega) hσ
  exact bracket_one_impossible_positive_quadrant
    P Q hpair ρ σ hdir (by omega) (by omega)

/-- The complete proper-power half of GGV Proposition 2.6, with no
restriction on the direction or mate, follows from the proved global
bracket-one exclusion and the existing descent/factorization theorem. -/
theorem ggv_proper_power_input_proved : GGVProperPowerInput :=
  ggv_proper_power_of_bracket_one_exclusion ggv_bracket_one_input_proved

end Dixmier.Weyl
