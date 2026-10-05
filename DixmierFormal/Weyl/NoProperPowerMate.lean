/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CommonPowerFactorization
public import DixmierFormal.Weyl.ProperPowerDescent
public import DixmierFormal.Weyl.HomogeneousRoot
public import DixmierFormal.Weyl.GGVCompanionAdapter
public import DixmierFormal.Weyl.TwoRootTotalDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact mate faces over a nonproper-power leading face

The zero-Poisson branch of the exact Weyl relation has no independent
factorization hypothesis: homogeneous Poisson commutation and the literal
nonproper-power condition force an integer face power.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- The precise remaining bracket-one source obligation: no counterexample
pair has leading Poisson bracket one in a primitive positive-sum direction.
It applies to every exact mate because mate subtraction preserves the
counterexample-pair predicate. -/
def GGVBracketOneInput : Prop :=
  ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
    ∀ ρ σ : ℤ, IsDirection ρ σ →
      poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 1

/-- In the bracket-one branch, the exact top-commutator law determines the
sum of the two positive operator weights. -/
theorem leading_weights_sum_of_bracket_one
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hpair : IsCounterexamplePair P Q)
    (hbr : poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 1) :
    vDeg ρ σ P.1 + vDeg ρ σ Q.1 = ρ + σ := by
  have hne : poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 0 := by
    rw [hbr]
    exact one_ne_zero
  have hdeg := (leadingForm_commutator P Q ρ σ hdir.2 hne).1
  rw [hpair.1, vDeg_one_A1] at hdeg
  omega

/-- A counterexample pair cannot have leading Poisson bracket one at a
positive-sum direction whose sum is one: both operand weights are positive
integers, while a nonzero top bracket would force their sum to equal one. -/
theorem bracket_one_impossible_of_unit_weight_sum
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hsum : ρ + σ = 1) (hpair : IsCounterexamplePair P Q) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ≠ 1 := by
  intro hbr
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hdeg := leading_weights_sum_of_bracket_one P Q ρ σ hdir hpair hbr
  omega

/-- At weight sum two, the only remaining bracket-one numerical pattern
has both operator weights equal to one. -/
theorem leading_weights_one_of_bracket_one_sum_two
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hsum : ρ + σ = 2) (hpair : IsCounterexamplePair P Q)
    (hbr : poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 1) :
    vDeg ρ σ P.1 = 1 ∧ vDeg ρ σ Q.1 = 1 := by
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hdeg := leading_weights_sum_of_bracket_one P Q ρ σ hdir hpair hbr
  omega

/-- In the total-degree direction, a bracket-one counterexample would have
both elements of PBW total degree one. This exposes the remaining degree-one
generation lemma needed to close this particular direction. -/
theorem bracket_one_diagonal_forces_totalDeg_one
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hbr : poisson (leadingForm 1 1 Q.1) (leadingForm 1 1 P.1) = 1) :
    totalDeg P.1 = 1 ∧ totalDeg Q.1 = 1 := by
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  obtain ⟨hP, hQ⟩ := leading_weights_one_of_bracket_one_sum_two
    P Q 1 1 hdir (by norm_num) hpair hbr
  have hPtotal := totalDeg_eq_vDeg_one_one P (by omega)
  have hQtotal := totalDeg_eq_vDeg_one_one Q (by omega)
  constructor <;> omega

/-- A PBW total-degree-one operator has no coefficient in total degree
two or higher. This is the coefficient-level input for the remaining
affine-pair generation argument. -/
theorem pbwCoeff_eq_zero_of_totalDeg_one
    (T : A1 ℂ) (hdeg : totalDeg T.1 = 1)
    (i j : ℕ) (hij : 2 ≤ i + j) :
    pbwCoeff T.1 i j = 0 := by
  by_contra hn
  have hmem : expo i j ∈ (symbol T.1).support := by
    apply MvPolynomial.mem_support_iff.mpr
    simpa only [symbol_coeff_pbwCoeff] using hn
  have hbound := MvPolynomial.le_totalDegree hmem
  have hsum : (expo i j).sum (fun _ e => e) = i + j := by
    rw [Finsupp.sum_fintype (expo i j) (fun _ e => e) (by simp)]
    simp [Fin.sum_univ_two, expo]
  change (expo i j).sum (fun _ e => e) ≤ totalDeg T.1 at hbound
  rw [hsum, hdeg] at hbound
  omega

/-- Every coefficient of total degree at least two vanishes for either
member of the diagonal bracket-one candidate. -/
theorem bracket_one_diagonal_high_pbwCoeff_zero
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hbr : poisson (leadingForm 1 1 Q.1) (leadingForm 1 1 P.1) = 1)
    (i j : ℕ) (hij : 2 ≤ i + j) :
    pbwCoeff P.1 i j = 0 ∧ pbwCoeff Q.1 i j = 0 := by
  obtain ⟨hP, hQ⟩ := bracket_one_diagonal_forces_totalDeg_one P Q hpair hbr
  exact ⟨pbwCoeff_eq_zero_of_totalDeg_one P hP i j hij,
    pbwCoeff_eq_zero_of_totalDeg_one Q hQ i j hij⟩

/-- For an exact counterexample mate, a zero leading Poisson bracket and a
nonproper-power first face force the mate face to be a positive integer
power, with the matching weighted degree. -/
theorem zero_poisson_mate_power_of_no_proper_power
    (P T : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hpair : IsCounterexamplePair P T)
    (hbr : poisson (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) = 0)
    (hnot : ∀ d : ℕ, 1 < d →
      ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ), μ ≠ 0 →
        leadingForm ρ σ P.1 ≠ MvPolynomial.C μ * S ^ d) :
    ∃ (ν : ℂ) (n : ℕ), ν ≠ 0 ∧
      vDeg ρ σ T.1 = ((n + 1 : ℕ) : ℤ) * vDeg ρ σ P.1 ∧
      leadingForm ρ σ T.1 = ν • (leadingForm ρ σ P.1) ^ (n + 1) := by
  have hPpos := counterexample_vDeg_pos_all_directions P T hpair ρ σ hdir
  have hTpos := counterexample_vDeg_pos_all_directions T (-P)
    (isCounterexamplePair_swap_neg P T hpair) ρ σ hdir
  let m : ℕ := (vDeg ρ σ P.1).toNat
  let ω : ℕ := (vDeg ρ σ T.1).toNat
  have hm : 0 < m := by omega
  have hω : 0 < ω := by omega
  have hmcast : (m : ℤ) = vDeg ρ σ P.1 := by omega
  have hωcast : (ω : ℤ) = vDeg ρ σ T.1 := by omega
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous (wt ρ σ) m := by
    rw [hmcast]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hThom : (leadingForm ρ σ T.1).IsWeightedHomogeneous (wt ρ σ) ω := by
    rw [hωcast]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T.1) (w := wt ρ σ) (n := vDeg ρ σ T.1)
  obtain ⟨ν, k, hν, hk, hface⟩ :=
    homogeneous_poisson_scalar_power_of_no_proper_power
      (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) ρ σ m ω
      hm hω (leadingForm_ne_zero_of_vDeg_pos T ρ σ hTpos)
      (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos)
      hThom hPhom hbr hnot
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    simp [hkzero] at hk
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  refine ⟨ν, n, hν, ?_, ?_⟩
  · rw [← hωcast, ← hmcast, hk]
    push_cast
    ring
  · simpa only [MvPolynomial.smul_eq_C_mul] using hface

/-- The source's proper-power mechanism, with its bracket-one exclusion
isolated as the remaining hypothesis. The conclusion here deliberately
does not yet assert that the root is weighted homogeneous. -/
theorem counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hpair : IsCounterexamplePair P Q)
    (hone : ∀ T : A1 ℂ, IsCounterexamplePair P T →
      poisson (leadingForm ρ σ T.1) (leadingForm ρ σ P.1) ≠ 1) :
    ∃ (d : ℕ) (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
      1 < d ∧ μ ≠ 0 ∧ leadingForm ρ σ P.1 = MvPolynomial.C μ * S ^ d := by
  by_contra hn
  have hnot : ∀ d : ℕ, 1 < d →
      ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ), μ ≠ 0 →
        leadingForm ρ σ P.1 ≠ MvPolynomial.C μ * S ^ d := by
    intro d hd S μ hμ heq
    exact hn ⟨d, S, μ, hd, hμ, heq⟩
  apply counterexample_impossible_of_power_face_descent P Q ρ σ hdir hpair hone
  intro T hT hbr
  exact zero_poisson_mate_power_of_no_proper_power P T ρ σ hdir hT hbr hnot

/-- The proper-power face conclusion is unconditional in every primitive
positive-sum direction of sum one. -/
theorem counterexample_face_scalar_proper_power_of_unit_weight_sum
    (P Q : A1 ℂ) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hsum : ρ + σ = 1) (hpair : IsCounterexamplePair P Q) :
    ∃ (d : ℕ) (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
      1 < d ∧ μ ≠ 0 ∧ leadingForm ρ σ P.1 = MvPolynomial.C μ * S ^ d := by
  apply counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion
    P Q ρ σ hdir hpair
  intro T hT
  exact bracket_one_impossible_of_unit_weight_sum P T ρ σ hdir hsum hT

/-- The proved sum-one branch includes a homogeneous root, so it is
the exact proper-power half of GGV Proposition 2.6 on these directions. -/
theorem ggv_proper_power_unit_weight_sum
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) (hsum : ρ + σ = 1) :
    ∃ (μ : ℂ) (k : ℕ) (R : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) R m ∧
      leadingForm ρ σ P.1 = C μ * R ^ k := by
  obtain ⟨d, S, μ, hd, hμ, hface⟩ :=
    counterexample_face_scalar_proper_power_of_unit_weight_sum
      P Q ρ σ hdir hsum hpair
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

/-- The exact GGV proper-power field follows once the bracket-one
alternative has been excluded for every mate produced by descent. The
weighted-homogeneous root is derived, not assumed. -/
theorem ggv_proper_power_of_bracket_one_exclusion
    (hone : GGVBracketOneInput) :
    GGVProperPowerInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨d, S, μ, hd, hμ, hface⟩ :=
    counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion
      P Q ρ σ hdir hpair (fun T hT => hone P T hT ρ σ hdir)
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

/-- The frozen GGV companion conclusion from exactly two remaining source
obligations: exclusion of the bracket-one alternative and G13's preliminary
operator companion. All algebraic factorization, descent, and PBW-symbol
translation between them is proved locally. -/
theorem ggv_companion_of_bracket_one_and_operator_source
    (hone : GGVBracketOneInput)
    (hoperator : GGVOperatorPreliminaryInput) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
        leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R :=
  ggv_companion_of_operator_source_inputs
    (ggv_proper_power_of_bracket_one_exclusion hone) hoperator

end Dixmier.Weyl
