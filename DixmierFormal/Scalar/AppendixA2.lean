/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA1

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proposition A.2: normalized companion equation

This file proves the differential equation for the `A=1`, linear-`C`
factorization. The arbitrary-degree coefficient recurrence and full-support
conclusion of Proposition A.2 remain to be formalized.
-/

namespace Dixmier
open Polynomial

theorem appendix_A2_normalized_equation {ρ s : ℕ} {B : ℂ[X]}
    (hfactor : X*(X-1)*(C ((ρ : ℂ)-2*(s : ℂ))*derivative B) -
      B*(C (ρ : ℂ)*X+(X-1)) = 1)
    (hdeg : ((ρ : ℤ)-2*(s : ℤ)) * (B.natDegree : ℤ) = (ρ : ℤ)+1) :
    C ((ρ : ℂ)-2*(s : ℂ))*X*(X-1)*derivative B -
      (C (((ρ : ℂ)-2*(s : ℂ))*(B.natDegree : ℂ))*X-1)*B = 1 := by
  have hc : ((ρ : ℂ)-2*(s : ℂ))*(B.natDegree : ℂ) = (ρ : ℂ)+1 := by
    exact_mod_cast hdeg
  calc
    _ = X*(X-1)*(C ((ρ : ℂ)-2*(s : ℂ))*derivative B) -
          B*(C (ρ : ℂ)*X+(X-1)) := by rw [hc]; simp only [map_add, map_one]; ring
    _ = 1 := hfactor

theorem appendix_A2_equation_from_comp {ρ s : ℕ} {B : ℂ[X]}
    (hsρ : s < ρ) (hB : B ≠ 0) (hD : 0 < B.natDegree)
    (h : Comp ρ s (B^2) (B*(X-1))) :
    C ((ρ : ℂ)-2*(s : ℂ))*X*(X-1)*derivative B -
      (C (((ρ : ℂ)-2*(s : ℂ))*(B.natDegree : ℂ))*X-1)*B = 1 := by
  have hfactor := factor_equation_of_companion (ρ : ℤ) (s : ℤ)
    (1 : ℂ[X]) B (X-1) one_ne_zero hB
    ((companionEq_natCast_iff ρ s (1*B^2) (1*B*(X-1))).mpr (by simpa using h))
  have hdegree := appendix_factor_degree_identity ρ s (1 : ℂ[X]) B (X-1)
    hsρ one_ne_zero hB (by simpa only [C_1] using X_sub_C_ne_zero (1 : ℂ)) hD
      (by simpa using h)
  have hXdeg : (X-1 : ℂ[X]).natDegree = 1 := by
    simpa only [C_1] using natDegree_X_sub_C (1 : ℂ)
  have hdegree' : ((ρ : ℤ)-2*(s : ℤ)) * (B.natDegree : ℤ) = (ρ : ℤ)+1 := by
    rw [hXdeg] at hdegree
    simpa using hdegree
  apply appendix_A2_normalized_equation
  · simpa [derivative_sub, derivative_X, derivative_one, derivative_one, map_sub,
      map_one, mul_assoc] using hfactor
  · exact hdegree'

end Dixmier
