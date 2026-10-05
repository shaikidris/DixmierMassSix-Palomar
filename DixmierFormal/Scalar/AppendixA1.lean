/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixFullFactor
public import DixmierFormal.Scalar.AppendixFactorDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.1: exact factorization and degree consequences

The theorem has the paper's scalar companion assumptions, a multiplicity
bound of two for every root, and the existence of one double root. It
returns the normalized squarefree pairwise-coprime factors, positive
degree of the double-root factor, positive `ρ-2s`, the degree identity,
and the differential factor equation. No degree or support cutoff is used.
-/

namespace Dixmier
open Polynomial

/-- A double root of `r=A B²` forces positive degree of `B` when `A`
divides the separable companion `f`. -/
theorem appendix_B_degree_pos {r f A B Cc : ℂ[X]} {α : ℂ}
    (hfsep : f.Separable) (hf : f = A*B*Cc)
    (hr : r = A*B^2) (hB0 : B.eval 0 = 1)
    (hdouble : 2 ≤ rootMultiplicity α r) : 0 < B.natDegree := by
  by_contra hnot
  have hBdeg : B.natDegree = 0 := by omega
  have hB1 : B = 1 := by
    rw [eq_C_of_natDegree_eq_zero hBdeg, coeff_zero_eq_eval_zero, hB0, C_1]
  have hA_dvd : A ∣ f := by
    refine ⟨B*Cc, ?_⟩
    simpa [mul_assoc] using hf
  have hAsep : A.Separable := hfsep.of_dvd hA_dvd
  rw [hr, hB1] at hdouble
  simp only [one_pow, mul_one] at hdouble
  have hA1 := rootMultiplicity_le_one_of_separable hAsep α
  omega

/-- The complete statement of Proposition A.1 under its Appendix A root
multiplicity and companion hypotheses. -/
theorem appendix_A1_complete {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2)
    (hdouble : ∃ α : ℂ, 2 ≤ rootMultiplicity α r) :
    ∃ A B Cc : ℂ[X],
      A.eval 0 = 1 ∧ B.eval 0 = 1 ∧ Cc.eval 0 = -1 ∧
      Squarefree A ∧ Squarefree B ∧ Squarefree Cc ∧
      IsCoprime A B ∧ IsCoprime A Cc ∧ IsCoprime B Cc ∧
      r = A*B^2 ∧ f = A*B*Cc ∧ 0 < B.natDegree ∧ 2*s < ρ ∧
      ((ρ : ℤ)-2*(s : ℤ)) * (B.natDegree : ℤ) =
        (s : ℤ)*A.natDegree + (ρ : ℤ)*Cc.natDegree + 1 ∧
      X*Cc*(C ((ρ : ℂ)-2*(s : ℂ))*A*derivative B - C (s : ℂ)*derivative A*B) -
        A*B*(C (ρ : ℂ)*X*derivative Cc+Cc) = 1 := by
  obtain ⟨A,B,Cc,hA0,hB0,hC0,hAsq,hBsq,hCsq,hAB,hAC,hBC,hr,hf⟩ :=
    appendix_full_factorization h hsρ hr0 hq
  have hsep : f.Separable := h.companion_separable hsρ hr0
  obtain ⟨α,hα⟩ := hdouble
  have hD := appendix_B_degree_pos hsep hf hr hB0 hα
  have hAne : A ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hA0
    norm_num at hA0
  have hBne : B ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hB0
    norm_num at hB0
  have hCne : Cc ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hC0
    norm_num at hC0
  have hcomp' : Comp ρ s (A*B^2) (A*B*Cc) := by
    simpa only [hr,hf] using h
  have hpos := appendix_factor_h_pos ρ s A B Cc hsρ hAne hBne hCne hD hcomp'
  have hdegree := appendix_factor_degree_identity ρ s A B Cc hsρ hAne hBne hCne hD hcomp'
  have hCE : CompanionEq (ρ : ℤ) (s : ℤ) (A*B^2) (A*B*Cc) :=
    (companionEq_natCast_iff ρ s (A*B^2) (A*B*Cc)).mpr hcomp'
  have hfactor := factor_equation_of_companion (ρ : ℤ) (s : ℤ) A B Cc hAne hBne hCE
  refine ⟨A,B,Cc,hA0,hB0,hC0,hAsq,hBsq,hCsq,hAB,hAC,hBC,hr,hf,hD,hpos,hdegree,?_⟩
  simpa using hfactor

end Dixmier
