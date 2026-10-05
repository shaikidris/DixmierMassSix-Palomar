/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixFactorEquation
public import DixmierFormal.Scalar.Companion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Degree consequences of the Appendix A factorization

Given `r = A B²`, `f = A B C` and positive degree of `B`, the general
companion-degree identity yields equation (A.1) and `ρ - 2s > 0`. The
existence, normalization and squarefreeness of these factors are separate.
-/

namespace Dixmier
open Polynomial

/-- The degree identity `h D = s a + ρ c + 1` in Proposition A.1, conditional
on the displayed factorization. -/
theorem appendix_factor_degree_identity (ρ s : ℕ) (A B Cc : ℂ[X])
    (hsρ : s < ρ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : Cc ≠ 0)
    (hD : 0 < B.natDegree)
    (h : Comp ρ s (A*B^2) (A*B*Cc)) :
    ((ρ : ℤ)-2*(s : ℤ)) * (B.natDegree : ℤ) =
      (s : ℤ)*A.natDegree + (ρ : ℤ)*Cc.natDegree + 1 := by
  have hrdeg : (A*B^2).natDegree = A.natDegree + 2*B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero _ hB), natDegree_pow]
  have hfdeg : (A*B*Cc).natDegree = A.natDegree+B.natDegree+Cc.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) hC, natDegree_mul hA hB]
  have hrpos : 0 < (A*B^2).natDegree := by omega
  have hfpos : 0 < (A*B*Cc).natDegree := by omega
  have hid := h.degree_identity hsρ hrpos hfpos
  rw [hrdeg, hfdeg] at hid
  have hidz : (((ρ - s) * (A.natDegree+2*B.natDegree) : ℕ) : ℤ) =
      ((1 + ρ*(A.natDegree+B.natDegree+Cc.natDegree) : ℕ) : ℤ) := by
    exact_mod_cast hid
  rw [Nat.cast_mul, Nat.cast_sub hsρ.le] at hidz
  push_cast at hidz
  nlinarith

/-- The same degree identity forces the root-defect parameter `h=ρ-2s`
to be positive. -/
theorem appendix_factor_h_pos (ρ s : ℕ) (A B Cc : ℂ[X])
    (hsρ : s < ρ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : Cc ≠ 0)
    (hD : 0 < B.natDegree)
    (h : Comp ρ s (A*B^2) (A*B*Cc)) : 2*s < ρ := by
  have hid := appendix_factor_degree_identity ρ s A B Cc hsρ hA hB hC hD h
  by_contra hnot
  have hfactor : (ρ : ℤ) - 2*(s : ℤ) ≤ 0 := by omega
  have hDint : (0 : ℤ) ≤ (B.natDegree : ℤ) := by positivity
  have hprod := mul_nonpos_of_nonpos_of_nonneg hfactor hDint
  have ha : (0 : ℤ) ≤ A.natDegree := by positivity
  have hc : (0 : ℤ) ≤ Cc.natDegree := by positivity
  have hs : (0 : ℤ) ≤ s := by positivity
  have hρ : (0 : ℤ) ≤ ρ := by positivity
  nlinarith

end Dixmier
