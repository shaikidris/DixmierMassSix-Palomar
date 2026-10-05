/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFaceFirstTilt

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Rational slopes of actual polynomial Weyl faces

The finite first-tilt construction uses rational weights. This file
identifies those weights with the actual integer-normal leading faces.
-/

namespace Dixmier.Weyl

/-- The rational weight at normalized slope `t`. -/
def rationalNewtonWeight (t : ℚ) (a : Fin 2 →₀ ℕ) : ℚ :=
  (a 0 : ℚ) + t * (a 1 : ℚ)

private theorem rationalNewtonWeight_cast_real (t : ℚ)
    (a : Fin 2 →₀ ℕ) :
    ((rationalNewtonWeight t a : ℚ) : ℝ) =
      realNewtonWeight 1 (t : ℝ) a := by
  simp [rationalNewtonWeight, realNewtonWeight]

/-- A positive-first-coordinate integer leading face is exactly the
maximizing face at its rational normalized slope. -/
theorem leadingForm_mem_iff_rational_slope
    (P : A1 ℂ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (a : Fin 2 →₀ ℕ) :
    a ∈ (leadingForm ρ σ P.1).support ↔
      a ∈ (symbol P.1).support ∧
        ∀ b ∈ (symbol P.1).support,
          rationalNewtonWeight ((σ : ℚ) / ρ) b ≤
            rationalNewtonWeight ((σ : ℚ) / ρ) a := by
  rw [leadingForm_mem_normalized_real_face P ρ σ hρ]
  have ht : (((σ : ℚ) / ρ : ℚ) : ℝ) = (σ : ℝ) / ρ := by
    norm_num
  constructor
  · rintro ⟨ha,hmax⟩
    refine ⟨ha,?_⟩
    intro b hb
    have h := hmax b hb
    rw [← ht] at h
    rw [← rationalNewtonWeight_cast_real,
      ← rationalNewtonWeight_cast_real] at h
    exact_mod_cast h
  · rintro ⟨ha,hmax⟩
    refine ⟨ha,?_⟩
    intro b hb
    have h := hmax b hb
    have hreal :
        ((rationalNewtonWeight ((σ : ℚ) / ρ) b : ℚ) : ℝ) ≤
          ((rationalNewtonWeight ((σ : ℚ) / ρ) a : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [rationalNewtonWeight_cast_real,
      rationalNewtonWeight_cast_real, ht] at hreal
    exact hreal

/-- If an actual leading face has a last derivative-order point `a`
and the whole support has a higher-order point, there is a first
higher rational slope whose exposed face contains `a` and a higher
point. The statement does not yet identify this slope with the next
primitive face direction of the ordered G13 list. -/
theorem leadingFace_exists_first_upward_tilt
    (P : A1 ℂ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm ρ σ P.1).support)
    (hlast : ∀ p ∈ (leadingForm ρ σ P.1).support,
      p 1 ≤ a 1)
    (habove : ∃ p ∈ (symbol P.1).support, a 1 < p 1) :
    ∃ t : ℚ, (σ : ℚ) / ρ < t ∧
      (∀ p ∈ (symbol P.1).support,
        rationalNewtonWeight t p ≤ rationalNewtonWeight t a) ∧
      (∃ b ∈ (symbol P.1).support, a 1 < b 1 ∧
        rationalNewtonWeight t b = rationalNewtonWeight t a) := by
  let t₀ : ℚ := (σ : ℚ) / ρ
  let w : (Fin 2 →₀ ℕ) → ℚ := rationalNewtonWeight t₀
  have ha' := (leadingForm_mem_iff_rational_slope P ρ σ hρ a).mp ha
  have htop : ∀ p ∈ (symbol P.1).support, w p ≤ w a := by
    intro p hp
    exact ha'.2 p hp
  have hend : ∀ p ∈ (symbol P.1).support,
      w p = w a → p 1 ≤ a 1 := by
    intro p hp heq
    apply hlast p
    apply (leadingForm_mem_iff_rational_slope P ρ σ hρ p).mpr
    refine ⟨hp,?_⟩
    intro b hb
    exact (htop b hb).trans_eq heq.symm
  obtain ⟨δ,hδ,hbound,b,hb,hhigher,htie⟩ :=
    finiteSupport_exists_first_upward_tilt
      (symbol P.1).support (fun p => p 1) w (w a) (a 1)
      htop hend habove
  refine ⟨t₀ + δ, ?_, ?_, b,hb,hhigher,?_⟩
  · dsimp [t₀]
    linarith
  · intro p hp
    have h := hbound p hp
    dsimp [w] at h
    simpa [rationalNewtonWeight, mul_add, add_mul, add_assoc,
      add_comm, add_left_comm] using h
  · dsimp [w] at htie
    simpa [rationalNewtonWeight, mul_add, add_mul, add_assoc,
      add_comm, add_left_comm] using htie

end Dixmier.Weyl
