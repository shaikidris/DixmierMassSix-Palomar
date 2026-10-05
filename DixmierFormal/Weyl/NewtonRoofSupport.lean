/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedGradeBasic
public import Mathlib.Analysis.Convex.Hull

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Convex support of integer positive-sum Newton faces

This file formalizes a support-level part of the Newton-roof argument. We take the union of the
convex hulls of leading-face exponents over integer directions with positive weight sum. The
result is deliberately named as the integer-direction roof; identifying it with Han–Tan's full
real-direction roof requires a separate rational-direction/density argument.
-/

namespace Dixmier.Weyl

open Polynomial

/-- Embed a PBW exponent into the real plane. -/
def exponentPoint (d : Fin 2 →₀ ℕ) : ℝ × ℝ := ((d 0 : ℕ), (d 1 : ℕ))

/-- The union of convex hulls of leading-face supports over integer directions with positive
weight sum. -/
def integerPositiveNewtonRoof (T : Module.End ℂ ℂ[X]) : Set (ℝ × ℝ) :=
  {p | ∃ ρ σ : ℤ, 0 < ρ + σ ∧
    p ∈ convexHull ℝ
      (exponentPoint '' ((↑((leadingForm ρ σ T).support) : Set (Fin 2 →₀ ℕ))))}

/-- The cone of a set in the real plane, using nonnegative scalar multiples. -/
def positiveScalarCone (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∃ r : ℝ, 0 ≤ r ∧ ∃ q ∈ S, p = r • q}

private theorem exponentPoint_in_nonpositive_halfspace {d : Fin 2 →₀ ℕ}
    (h : grade d ≤ 0) :
    exponentPoint d ∈ {p : ℝ × ℝ | p.1 - p.2 ≤ 0} := by
  change ((d 0 : ℕ) : ℝ) - ((d 1 : ℕ) : ℝ) ≤ 0
  have hz : (d 0 : ℤ) - (d 1 : ℤ) ≤ 0 := by simpa [grade] using h
  exact_mod_cast hz

/-- If every PBW exponent has nonpositive grade, then every convex leading face in an integer
positive-sum direction lies in the same nonpositive half-plane. -/
theorem integerPositiveNewtonRoof_grade_nonpositive (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    integerPositiveNewtonRoof (T : Module.End ℂ ℂ[X]) ⊆
      {p : ℝ × ℝ | p.1 ≤ p.2} := by
  intro p hp
  rcases hp with ⟨ρ, σ, hρσ, hp⟩
  have hFace : ∀ d ∈ (leadingForm ρ σ (T : Module.End ℂ ℂ[X])).support,
      grade d ≤ 0 :=
    leadingForm_support_grade_bound (T : Module.End ℂ ℂ[X]) ρ σ 0 hT
  have hsubset :
      exponentPoint ''
        ((↑((leadingForm ρ σ (T : Module.End ℂ ℂ[X])).support) :
          Set (Fin 2 →₀ ℕ))) ⊆
        {q : ℝ × ℝ | q.1 - q.2 ≤ 0} := by
    rintro q ⟨d, hd, rfl⟩
    exact exponentPoint_in_nonpositive_halfspace (hFace d hd)
  have hconvex : Convex ℝ {q : ℝ × ℝ | q.1 - q.2 ≤ 0} :=
    convex_halfSpace_le IsLinearMap.isLinearMap_sub 0
  have hp' : p ∈ {q : ℝ × ℝ | q.1 - q.2 ≤ 0} :=
    convexHull_min hsubset hconvex hp
  change p.1 - p.2 ≤ 0 at hp'
  change p.1 ≤ p.2
  linarith

/-- Nonnegative scaling preserves the grade half-plane. -/
theorem positiveScalarCone_subset_nonpositive_halfspace (S : Set (ℝ × ℝ))
    (hS : S ⊆ {q : ℝ × ℝ | q.1 ≤ q.2}) :
    positiveScalarCone S ⊆ {p : ℝ × ℝ | p.1 ≤ p.2} := by
  rintro p ⟨r, hr, q, hq, rfl⟩
  have hq' : q.1 ≤ q.2 := hS hq
  change r * q.1 ≤ r * q.2
  exact mul_le_mul_of_nonneg_left hq' hr

/-- The cone over the integer positive Newton roof of a nonpositive-grade operator is also
contained in the nonpositive grade half-plane. -/
theorem integerPositiveNewtonRoof_cone_grade_nonpositive (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    positiveScalarCone (integerPositiveNewtonRoof (T : Module.End ℂ ℂ[X])) ⊆
      {p : ℝ × ℝ | p.1 ≤ p.2} :=
  positiveScalarCone_subset_nonpositive_halfspace _
    (integerPositiveNewtonRoof_grade_nonpositive T hT)

end Dixmier.Weyl
