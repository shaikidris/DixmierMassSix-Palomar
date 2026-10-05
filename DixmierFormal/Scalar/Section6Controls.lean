/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- The seven-term scalar boundary solution satisfies the companion equation. -/
theorem section6_cubic_companion :
    CompanionEq 2 1 ((1-X : ℂ[X])^3) (X-1) := by
  unfold CompanionEq
  simp only [derivative_pow, derivative_sub, derivative_one, derivative_X]
  push_cast
  simp only [map_sub, map_ofNat, map_one]
  ring

/-- The boundary solution has exactly seven terms in its square. -/
theorem section6_cubic_seven_terms :
    termCount ((((1-X : ℂ[X])^3)^2)) = 7 := by
  have hdeg : (1-X : ℂ[X]).natDegree ≤ 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    simp
  have hsign : ∀ n ≤ 1, ∃ x : ℝ, 0 < x ∧
      (1-X : ℂ[X]).coeff n = (((-1:ℝ)^n*x:ℝ):ℂ) := by
    intro n hn
    interval_cases n
    · refine ⟨1,by norm_num,?_⟩
      simp [coeff_sub, coeff_one]
    · refine ⟨1,by norm_num,?_⟩
      simp [coeff_sub, coeff_one]
  have htc := signed_dense_power_termCount hdeg hsign 6
  simpa only [← pow_mul] using htc

end Dixmier

namespace Dixmier
open Polynomial

theorem section6_imprimitive_expansion :
    ((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2 =
      1-6*X^6+4*X^9+9*X^12-12*X^15+4*X^18 := by
  ring

theorem section6_imprimitive_six_terms :
    termCount (((1-X^3 : ℂ[X])^4)*(1+2*X^3)^2) = 6 := by
  rw [section6_imprimitive_expansion]
  have hsupp : (1-6*X^6+4*X^9+9*X^12-12*X^15+4*X^18 : ℂ[X]).support =
      {0,6,9,12,15,18} := by
    ext n
    simp only [mem_support_iff, coeff_add, coeff_sub,
      coeff_one, Finset.mem_insert, Finset.mem_singleton]
    by_cases h0 : n = 0 <;> by_cases h6 : n = 6 <;>
      by_cases h9 : n = 9 <;> by_cases h12 : n = 12 <;>
      by_cases h15 : n = 15 <;> by_cases h18 : n = 18 <;>
      simp_all
  unfold termCount
  rw [hsupp]
  decide


end Dixmier

namespace Dixmier
open Polynomial

/-- The nonintegral parameter control satisfies the same polynomial equation
when `ρ = 5/2` and `s = 1`. -/
theorem section6_half_integral_companion :
    let r : ℂ[X] := (1+X^2)^2
    let f : ℂ[X] := -(1+X^2)
    C (((5:ℂ)/2)-1)*X*f*derivative r-
      (f+C ((5:ℂ)/2)*X*derivative f+1)*r=0 := by
  dsimp
  simp only [derivative_pow, derivative_add, derivative_one, derivative_X]
  norm_num
  simp only [map_ofNat]
  have hrat : -(4:ℂ[X])*C ((3:ℂ)/2)+1+2*C ((5:ℂ)/2)=0 := by
    have hs : -(4:ℂ)*((3:ℂ)/2)+1+2*((5:ℂ)/2)=0 := by norm_num
    have hc := congrArg (fun z : ℂ => (C z : ℂ[X])) hs
    simpa only [map_add, map_sub, map_neg, map_mul, map_ofNat, map_one, map_zero] using hc
  linear_combination (X^2+2*X^4+X^6)*hrat

end Dixmier
