/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedFaceSuccessor

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Paired adjacent Newton-face endpoints

The actual negative-face slope list is common to both members of an
exact counterexample pair. Consecutive faces therefore have shared
vertices for both members at the same two directions.
-/

namespace Dixmier.Weyl

/-- Consecutive primitive negative directions give shared occupied
vertices for both members of a counterexample pair, with no mate
order or degree bound. -/
theorem counterexample_paired_successor_shared_endpoints
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (hdir₁ : IsDirection ρ₁ σ₁) (hdir₂ : IsDirection ρ₂ σ₂)
    (hσ₁ : σ₁ < 0) (hσ₂ : σ₂ < 0)
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length)
    (hfirst : (ggvOrderedNegativeFaceSlopes P)[j] = (σ₁ : ℚ) / ρ₁)
    (hsecond : (ggvOrderedNegativeFaceSlopes P)[j+1] = (σ₂ : ℚ) / ρ₂)
    (hface₁ : InDir ρ₁ σ₁ P.1)
    (hface₂ : InDir ρ₂ σ₂ P.1) :
    (∃ a : Fin 2 →₀ ℕ,
      a ∈ (leadingForm ρ₁ σ₁ P.1).support ∧
      a ∈ (leadingForm ρ₂ σ₂ P.1).support ∧
      (∀ p ∈ (leadingForm ρ₁ σ₁ P.1).support, p 1 ≤ a 1) ∧
      (∀ p ∈ (leadingForm ρ₂ σ₂ P.1).support, a 1 ≤ p 1)) ∧
    (∃ b : Fin 2 →₀ ℕ,
      b ∈ (leadingForm ρ₁ σ₁ Q.1).support ∧
      b ∈ (leadingForm ρ₂ σ₂ Q.1).support ∧
      (∀ p ∈ (leadingForm ρ₁ σ₁ Q.1).support, p 1 ≤ b 1) ∧
      (∀ p ∈ (leadingForm ρ₂ σ₂ Q.1).support, b 1 ≤ p 1)) := by
  have hρ₁ : 0 < ρ₁ := by have := hdir₁.2; omega
  have hρ₂ : 0 < ρ₂ := by have := hdir₂.2; omega
  have hj0 : j < (ggvOrderedNegativeFaceSlopes P).length := by omega
  have hmem₁ : (ggvOrderedNegativeFaceSlopes P)[j] ∈
      ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj0
  have hmem₂ : (ggvOrderedNegativeFaceSlopes P)[j+1] ∈
      ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj
  have hleft : -1 < (σ₁ : ℚ) / ρ₁ := by
    rw [← hfirst]
    exact (ggv_ordered_negative_slope_bounds P _ hmem₁).1
  have hright : (σ₂ : ℚ) / ρ₂ < 0 := by
    rw [← hsecond]
    exact (ggv_ordered_negative_slope_bounds P _ hmem₂).2
  have hQface₁ :=
    (counterexample_strict_negative_InDir_iff
      P Q hpair ρ₁ σ₁ hdir₁ hσ₁).mp hface₁
  have hQface₂ :=
    (counterexample_strict_negative_InDir_iff
      P Q hpair ρ₂ σ₂ hdir₂ hσ₂).mp hface₂
  have hlist := ggv_ordered_negative_slopes_eq P Q hpair
  have hjQ : j + 1 < (ggvOrderedNegativeFaceSlopes Q).length := by
    rw [← hlist]
    exact hj
  have hfirstQ : (ggvOrderedNegativeFaceSlopes Q)[j] =
      (σ₁ : ℚ) / ρ₁ := by
    simpa only [← hlist] using hfirst
  have hsecondQ : (ggvOrderedNegativeFaceSlopes Q)[j+1] =
      (σ₂ : ℚ) / ρ₂ := by
    simpa only [← hlist] using hsecond
  constructor
  · exact leadingFace_successor_shared_endpoint
      P ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hleft hright
      j hj hfirst hsecond hface₁ hface₂
  · exact leadingFace_successor_shared_endpoint
      Q ρ₁ σ₁ ρ₂ σ₂ hρ₁ hρ₂ hleft hright
      j hjQ hfirstQ hsecondQ hQface₁ hQface₂

end Dixmier.Weyl
