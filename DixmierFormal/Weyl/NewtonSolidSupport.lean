/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NewtonRoofSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Solid Newton support from finite PBW support

The integer-direction roof consists of convex hulls of exposed subsets of the PBW support.
This file records its containment in the full support hull and the resulting one-sided grade
bound on diagonal solidifications. It does not identify the integer-direction roof with the
real-direction roof used by Han--Tan.
-/

namespace Dixmier.Weyl

open Polynomial

/-- The convex hull of all PBW exponent points of an operator. -/
def symbolNewtonPolygon (T : Module.End ℂ ℂ[X]) : Set (ℝ × ℝ) :=
  convexHull ℝ (exponentPoint '' ((symbol T).support : Set (Fin 2 →₀ ℕ)))

/-- The diagonal solidification of the support hull, restricted to the nonnegative quadrant. -/
def solidSymbolNewtonPolygon (T : Module.End ℂ ℂ[X]) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ t : ℝ, 0 ≤ t ∧ p + t • (1, 1) ∈ symbolNewtonPolygon T}

private theorem exponentPoint_in_nonpositive_halfspace' {d : Fin 2 →₀ ℕ}
    (h : grade d ≤ 0) :
    exponentPoint d ∈ {p : ℝ × ℝ | p.1 - p.2 ≤ 0} := by
  change ((d 0 : ℕ) : ℝ) - ((d 1 : ℕ) : ℝ) ≤ 0
  have hz : (d 0 : ℤ) - (d 1 : ℤ) ≤ 0 := by simpa [grade] using h
  exact_mod_cast hz

/-- Every integer-direction exposed face lies in the convex hull of the complete PBW support. -/
theorem integerPositiveNewtonRoof_subset_symbolNewtonPolygon
    (T : Module.End ℂ ℂ[X]) :
    integerPositiveNewtonRoof T ⊆ symbolNewtonPolygon T := by
  intro p hp
  rcases hp with ⟨ρ, σ, hsum, hp⟩
  have hface : (exponentPoint ''
      ((↑((leadingForm ρ σ T).support) : Set (Fin 2 →₀ ℕ)))) ⊆
      exponentPoint '' ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    rintro q ⟨d, hd, rfl⟩
    exact ⟨d, leadingForm_support_subset_symbol_support T ρ σ hd, rfl⟩
  exact (convexHull_mono hface) hp

private theorem symbolNewtonPolygon_grade_nonpositive (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    symbolNewtonPolygon (T : Module.End ℂ ℂ[X]) ⊆
      {p : ℝ × ℝ | p.1 ≤ p.2} := by
  have hsubset : exponentPoint ''
      ((↑((symbol (T : Module.End ℂ ℂ[X])).support) : Set (Fin 2 →₀ ℕ))) ⊆
      {p : ℝ × ℝ | p.1 - p.2 ≤ 0} := by
    rintro q ⟨d, hd, rfl⟩
    exact exponentPoint_in_nonpositive_halfspace' (hT d hd)
  have hconvex : Convex ℝ {q : ℝ × ℝ | q.1 - q.2 ≤ 0} :=
    convex_halfSpace_le IsLinearMap.isLinearMap_sub 0
  intro p hp
  have hp' : p ∈ {q : ℝ × ℝ | q.1 - q.2 ≤ 0} :=
    convexHull_min hsubset hconvex hp
  change p.1 - p.2 ≤ 0 at hp'
  exact sub_nonpos.mp hp'

/-- The support hull lies in the nonnegative quadrant because every PBW exponent does. -/
theorem symbolNewtonPolygon_nonnegative (T : Module.End ℂ ℂ[X]) {p : ℝ × ℝ}
    (hp : p ∈ symbolNewtonPolygon T) : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have hfst : IsLinearMap ℝ (fun q : ℝ × ℝ => q.1) :=
    ⟨by intro x y; rfl, by intro a x; rfl⟩
  have hsnd : IsLinearMap ℝ (fun q : ℝ × ℝ => q.2) :=
    ⟨by intro x y; rfl, by intro a x; rfl⟩
  have hfirst : exponentPoint ''
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) ⊆ {q : ℝ × ℝ | 0 ≤ q.1} := by
    rintro q ⟨d, hd, rfl⟩
    change 0 ≤ ((d 0 : ℕ) : ℝ)
    exact_mod_cast (Nat.zero_le (d 0))
  have hsecond : exponentPoint ''
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) ⊆ {q : ℝ × ℝ | 0 ≤ q.2} := by
    rintro q ⟨d, hd, rfl⟩
    change 0 ≤ ((d 1 : ℕ) : ℝ)
    exact_mod_cast (Nat.zero_le (d 1))
  constructor
  · exact convexHull_min hfirst (convex_halfSpace_ge hfst 0) hp
  · exact convexHull_min hsecond (convex_halfSpace_ge hsnd 0) hp

/-- The solid Newton polygon of an operator supported in nonpositive grades remains in that
same grade half-plane. Diagonal downward shifts preserve the difference of the coordinates. -/
theorem solidSymbolNewtonPolygon_grade_nonpositive (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    solidSymbolNewtonPolygon (T : Module.End ℂ ℂ[X]) ⊆
      {p : ℝ × ℝ | p.1 ≤ p.2} := by
  rintro p ⟨hp₁, hp₂, t, ht, hq⟩
  have hq' := symbolNewtonPolygon_grade_nonpositive T hT hq
  have hcoords : p.1 + t ≤ p.2 + t := by simpa using hq'
  exact (add_le_add_iff_right t).mp hcoords

/-- The solid Newton polygon lies on the grade-nonpositive side exactly when the original PBW
support does. This is the one-sided support/polygon equivalence used in the roof argument. -/
theorem solidSymbolNewtonPolygon_grade_nonpositive_iff (T : A1 ℂ) :
    (∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) ↔
      solidSymbolNewtonPolygon (T : Module.End ℂ ℂ[X]) ⊆
        {p : ℝ × ℝ | p.1 ≤ p.2} := by
  constructor
  · exact solidSymbolNewtonPolygon_grade_nonpositive T
  · intro h d hd
    have hmem : exponentPoint d ∈
        solidSymbolNewtonPolygon (T : Module.End ℂ ℂ[X]) := by
      refine ⟨?_, ?_, 0, le_rfl, ?_⟩
      · change 0 ≤ ((d 0 : ℕ) : ℝ)
        exact_mod_cast (Nat.zero_le (d 0))
      · change 0 ≤ ((d 1 : ℕ) : ℝ)
        exact_mod_cast (Nat.zero_le (d 1))
      have hpoint : exponentPoint d ∈
          exponentPoint '' ((symbol (T : Module.End ℂ ℂ[X])).support : Set (Fin 2 →₀ ℕ)) :=
        ⟨d, hd, rfl⟩
      simpa [symbolNewtonPolygon] using
        (subset_convexHull ℝ
          (exponentPoint '' ((symbol (T : Module.End ℂ ℂ[X])).support :
            Set (Fin 2 →₀ ℕ))) hpoint)
    have hp := h hmem
    change ((d 0 : ℕ) : ℝ) ≤ ((d 1 : ℕ) : ℝ) at hp
    have hnat : d 0 ≤ d 1 := by exact_mod_cast hp
    have hz : (d 0 : ℤ) - (d 1 : ℤ) ≤ 0 := by omega
    simpa [grade] using hz

/-- An integer-direction roof point belongs to the corresponding solid Newton polygon whenever
it is already in the nonnegative quadrant. -/
theorem integerRoof_point_mem_solidSymbolNewtonPolygon
    (T : Module.End ℂ ℂ[X]) {p : ℝ × ℝ}
    (hp : p ∈ integerPositiveNewtonRoof T) :
    p ∈ solidSymbolNewtonPolygon T := by
  have hpoly : p ∈ symbolNewtonPolygon T :=
    integerPositiveNewtonRoof_subset_symbolNewtonPolygon T hp
  rcases symbolNewtonPolygon_nonnegative T hpoly with ⟨hp₁, hp₂⟩
  refine ⟨hp₁, hp₂, 0, le_rfl, ?_⟩
  simpa [symbolNewtonPolygon] using hpoly

end Dixmier.Weyl
