/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FourierBoundarySupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exact occupancy of a Fourier boundary endpoint

A missing swapped endpoint would give a strict row bound. Four successive
boundary transports contradict the original occupied endpoint.
-/
namespace Dixmier.Weyl

/-- Highest-row bounds become rightmost-column bounds under Fourier. -/
theorem fourier_highest_row_boundary_bounds
    (P : A1 ℂ) (a b : ℕ)
    (hy : ∀ d ∈ (symbol P.1).support, d 1 ≤ a)
    (hx : ∀ d ∈ (symbol P.1).support, d 1 = a → d 0 ≤ b) :
    (∀ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 0 ≤ a) ∧
      (∀ d ∈ (symbol (fourierAlgHom ℂ P).1).support, d 0 = a → d 1 ≤ b) := by
  refine ⟨fourier_support_first_coord_le_of_second P a hy,?_⟩
  intro d hd heq
  obtain ⟨i,j,k,horig,hki,hkj,rfl⟩ := fourier_support_precursor P d hd
  have hj := hy (expo i j) horig
  simp [expo] at hj heq ⊢
  have hjk : j = a ∧ k = 0 := by omega
  have hi := hx (expo i j) horig (by simpa [expo] using hjk.1)
  simp [expo] at hi
  omega

/-- Fourier preserves occupancy of the transposed rightmost-column endpoint. -/
theorem fourier_rightmost_column_endpoint_mem
    (P : A1 ℂ) (a b : ℕ) (ha : 0 < a)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ a)
    (hy : ∀ d ∈ (symbol P.1).support, d 0 = a → d 1 ≤ b) :
    expo b a ∈ (symbol (fourierAlgHom ℂ P).1).support := by
  classical
  let F := fourierAlgHom ℂ
  obtain ⟨hFy,hFx⟩ := fourier_rightmost_column_boundary_bounds P a b hx hy
  by_contra hn
  by_cases hb : b = 0
  · obtain ⟨d,hd,he⟩ := fourier_attains_rightmost_column_height P a b ha hpoint hx
    have hzero := hFx d hd he
    have hdEq : d = expo b a := by
      ext t
      fin_cases t <;> simp [expo,hb] at * <;> omega
    exact hn (hdEq ▸ hd)
  · have hstrict : ∀ d ∈ (symbol (F P).1).support, d 1 = a → d 0 ≤ b-1 := by
      intro d hd he
      have hle := hFx d hd he
      have hne : d 0 ≠ b := by
        intro heq
        have hdEq : d = expo b a := by
          ext t
          fin_cases t <;> simp [expo] <;> assumption
        exact hn (hdEq ▸ hd)
      omega
    obtain ⟨h2x,h2y⟩ := fourier_highest_row_boundary_bounds (F P) a (b-1) hFy hstrict
    obtain ⟨h3y,h3x⟩ := fourier_rightmost_column_boundary_bounds (F (F P)) a (b-1) h2x h2y
    obtain ⟨h4x,h4y⟩ := fourier_highest_row_boundary_bounds (F (F (F P))) a (b-1) h3y h3x
    have horig : ∀ d ∈ (symbol P.1).support, d 0 = a → d 1 ≤ b-1 := by
      simpa only [F,fourierAlgHom_fourth] using h4y
    have hbad := horig (expo a b) hpoint (by simp [expo])
    simp [expo] at hbad
    omega

end Dixmier.Weyl
