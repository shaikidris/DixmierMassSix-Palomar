/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedFaceDirections

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Order geometry between distinct Newton faces

As the normalized slope increases, the derivative exponent of an
exposed support point cannot decrease. This is a support-level step
toward identifying the shared vertex of consecutive faces.
-/

namespace Dixmier.Weyl

/-- Exposed points at increasing normalized slopes have nondecreasing
second coordinate. If the coordinates tie, the two points coincide. -/
theorem real_exposed_points_ordered
    (S : Set (Fin 2 →₀ ℕ)) (t₁ t₂ : ℝ)
    (hlt : t₁ < t₂) {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ realExposedFace 1 t₁ S)
    (hb : b ∈ realExposedFace 1 t₂ S) :
    a 1 ≤ b 1 ∧ (a 1 = b 1 → a = b) := by
  have hab := ha.2 b hb.1
  have hba := hb.2 a ha.1
  dsimp [realNewtonWeight] at hab hba
  have hy : (a 1 : ℝ) ≤ (b 1 : ℝ) := by
    by_contra h
    have hrev : (b 1 : ℝ) < a 1 := lt_of_not_ge h
    have hpos : 0 < (t₂ - t₁) * ((a 1 : ℝ) - b 1) :=
      mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hrev)
    nlinarith [hab,hba]
  constructor
  · exact_mod_cast hy
  · intro hyeq
    have hyeqR : (a 1 : ℝ) = b 1 := by exact_mod_cast hyeq
    have hxeqR : (a 0 : ℝ) = b 0 := by
      rw [hyeqR] at hab
      rw [hyeqR] at hba
      linarith [hab, hba]
    have hxeq : a 0 = b 0 := by exact_mod_cast hxeqR
    ext i
    fin_cases i
    · exact hxeq
    · exact hyeq

/-- An actual positive-first-coordinate integer face is the exposed
face of its normalized real slope. -/
theorem leadingForm_mem_normalized_real_face
    (P : A1 ℂ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (a : Fin 2 →₀ ℕ) :
    a ∈ (leadingForm ρ σ P.1).support ↔
      a ∈ realExposedFace 1 ((σ : ℝ) / ρ)
        ((symbol P.1).support : Set (Fin 2 →₀ ℕ)) := by
  rw [leadingForm_mem_iff_realExposedFace]
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hscale := realExposedFace_pos_scale (ρ : ℝ) 1
    ((σ : ℝ) / ρ) hρR
    ((symbol P.1).support : Set (Fin 2 →₀ ℕ))
  have hmul : (ρ : ℝ) * ((σ : ℝ) / ρ) = σ := by
    field_simp [ne_of_gt hρR]
  have hset :
      realExposedFace (ρ : ℝ) (σ : ℝ)
        ((symbol P.1).support : Set (Fin 2 →₀ ℕ)) =
      realExposedFace 1 ((σ : ℝ) / ρ)
        ((symbol P.1).support : Set (Fin 2 →₀ ℕ)) := by
    simpa only [mul_one, hmul] using hscale
  rw [hset]

/-- On two actual leading faces ordered by slope, the second
coordinates of occupied PBW exponents cannot run backwards. -/
theorem leadingFace_points_ordered_by_slope
    (P : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hlt : (σ₁ : ℝ) / ρ₁ < (σ₂ : ℝ) / ρ₂)
    {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ (leadingForm ρ₁ σ₁ P.1).support)
    (hb : b ∈ (leadingForm ρ₂ σ₂ P.1).support) :
    a 1 ≤ b 1 ∧ (a 1 = b 1 → a = b) := by
  exact real_exposed_points_ordered
    ((symbol P.1).support : Set (Fin 2 →₀ ℕ))
    ((σ₁ : ℝ) / ρ₁) ((σ₂ : ℝ) / ρ₂) hlt
    ((leadingForm_mem_normalized_real_face P ρ₁ σ₁ hρ₁ a).mp ha)
    ((leadingForm_mem_normalized_real_face P ρ₂ σ₂ hρ₂ b).mp hb)

end Dixmier.Weyl
