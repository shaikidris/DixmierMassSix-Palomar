/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCommonFaceDirections
public import Mathlib.Data.Finset.Sort

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Ordered slopes of actual common negative Newton faces

The finite primitive direction set of a counterexample pair has an
injective rational slope map. This module chooses the increasing list
of those slopes, proves exact coverage, and places every entry strictly
between the horizontal and diagonal boundary slopes. Geometric links
between consecutive faces are not asserted here.
-/

namespace Dixmier.Weyl

/-- The source-facing finite carrier of genuine primitive negative
face directions of an actual polynomial Weyl operator. -/
def ggvNegativePrimitiveDirections (P : A1 ℂ) : Set (ℤ × ℤ) :=
  {v | IsDirection v.1 v.2 ∧ 0 < v.1 ∧ v.2 < 0 ∧ InDir v.1 v.2 P.1}

/-- The rational slopes of the finite primitive direction carrier. -/
noncomputable def ggvNegativePrimitiveSlopes (P : A1 ℂ) : Finset ℚ :=
  ((ggv_negative_primitive_face_directions_finite P).image
    (fun v : ℤ × ℤ => (v.2 : ℚ) / (v.1 : ℚ))).toFinset

/-- The actual negative-face slopes in increasing order. -/
noncomputable def ggvOrderedNegativeFaceSlopes (P : A1 ℂ) : List ℚ :=
  (ggvNegativePrimitiveSlopes P).sort (· ≤ ·)

theorem ggv_ordered_negative_slopes_strict (P : A1 ℂ) :
    (ggvOrderedNegativeFaceSlopes P).SortedLT := by
  exact Finset.sortedLT_sort _

/-- An entry occurs exactly when it is the slope of an actual primitive
negative leading face. -/
theorem mem_ggvOrderedNegativeFaceSlopes_iff
    (P : A1 ℂ) (t : ℚ) :
    t ∈ ggvOrderedNegativeFaceSlopes P ↔
      ∃ v : ℤ × ℤ, v ∈ ggvNegativePrimitiveDirections P ∧
        t = (v.2 : ℚ) / (v.1 : ℚ) := by
  classical
  simp only [ggvOrderedNegativeFaceSlopes, Finset.mem_sort,
    ggvNegativePrimitiveSlopes, Set.Finite.mem_toFinset, Set.mem_image]
  constructor
  · rintro ⟨v,hv,hvt⟩
    exact ⟨v,hv,hvt.symm⟩
  · rintro ⟨v,hv,hvt⟩
    exact ⟨v,hv,hvt.symm⟩

/-- The ordered carrier is common to both exact members. -/
theorem ggv_ordered_negative_slopes_eq
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    ggvOrderedNegativeFaceSlopes P = ggvOrderedNegativeFaceSlopes Q := by
  have hsets : ggvNegativePrimitiveDirections P =
      ggvNegativePrimitiveDirections Q :=
    counterexample_strict_negative_direction_sets_eq P Q hpair
  have hslopes : ggvNegativePrimitiveSlopes P =
      ggvNegativePrimitiveSlopes Q := by
    apply Finset.ext
    intro t
    simp only [ggvNegativePrimitiveSlopes, Set.Finite.mem_toFinset,
      Set.mem_image]
    change (∃ x ∈ ggvNegativePrimitiveDirections P,
      (x.2 : ℚ) / (x.1 : ℚ) = t) ↔
      ∃ x ∈ ggvNegativePrimitiveDirections Q,
        (x.2 : ℚ) / (x.1 : ℚ) = t
    rw [hsets]
  simpa only [ggvOrderedNegativeFaceSlopes] using congrArg (fun s : Finset ℚ =>
    s.sort (· ≤ ·)) hslopes

/-- Every genuine strict-negative face slope lies strictly between the
horizontal slope zero and the diagonal slope minus one. -/
theorem ggv_ordered_negative_slope_bounds
    (P : A1 ℂ) (t : ℚ) (ht : t ∈ ggvOrderedNegativeFaceSlopes P) :
    -1 < t ∧ t < 0 := by
  obtain ⟨⟨ρ,σ⟩,⟨hdir,hρ,hσ,_⟩,rfl⟩ :=
    (mem_ggvOrderedNegativeFaceSlopes_iff P t).mp ht
  have hρQ : (0 : ℚ) < ρ := by exact_mod_cast hρ
  have hσQ : (σ : ℚ) < 0 := by exact_mod_cast hσ
  have hsumQ : (0 : ℚ) < ρ + σ := by exact_mod_cast hdir.2
  constructor
  · apply (lt_div_iff₀ hρQ).mpr
    nlinarith
  · exact div_neg_of_neg_of_pos hσQ hρQ

end Dixmier.Weyl
