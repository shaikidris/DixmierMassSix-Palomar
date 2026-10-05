/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFourierRectangle

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Fourier transport of support boundary bounds

A rightmost column becomes the highest row. Its row bound is transported
without requiring a global rectangle.
-/
namespace Dixmier.Weyl

/-- The rightmost-column endpoint bounds become highest-row bounds. -/
theorem fourier_rightmost_column_boundary_bounds
    (P : A1 ℂ) (a b : ℕ)
    (hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ a)
    (hy : ∀ d ∈ (symbol P.1).support, d 0 = a → d 1 ≤ b) :
    (∀ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 1 ≤ a) ∧
      (∀ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 1 = a → d 0 ≤ b) := by
  refine ⟨fourier_support_second_coord_le_of_first P a hx,?_⟩
  intro d hd heq
  obtain ⟨i,j,k,horig,hki,hkj,rfl⟩ := fourier_support_precursor P d hd
  have hi := hx (expo i j) horig
  simp [expo] at hi heq ⊢
  have hik : i = a ∧ k = 0 := by omega
  have hj := hy (expo i j) horig (by simpa [expo] using hik.1)
  simp [expo] at hj
  omega

/-- An occupied rightmost column forces the Fourier image to attain
exactly the corresponding Y-height. -/
theorem fourier_attains_rightmost_column_height
    (P : A1 ℂ) (a b : ℕ) (ha : 0 < a)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ a) :
    ∃ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 1 = a := by
  classical
  by_contra hn
  have hFy := fourier_support_second_coord_le_of_first P a hx
  have hsmaller : ∀ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 1 ≤ a-1 := by
    intro d hd
    have hle := hFy d hd
    have hne : d 1 ≠ a := by intro heq; exact hn ⟨d,hd,heq⟩
    omega
  have hback := support_first_coord_le_of_fourier_second P (a-1) hsmaller
  have hbad := hback (expo a b) hpoint
  simp [expo] at hbad
  omega

end Dixmier.Weyl
