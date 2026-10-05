/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveBinomialTopBoundary

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Axis diagonal with a negative top boundary

The actual positive face is constructed internally before applying the
mass bound. Companion and uniform degree inputs remain explicit.
-/
namespace Dixmier.Weyl

/-- An axis-only diagonal and a negative rightmost highest-row endpoint
force mass at least ten. No face shape or positive slope is assumed. -/
theorem preliminary_axis_diagonal_negative_top_mass_ge_ten
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) (n : ℕ)
    (hmem : expo n 0 ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo n 0)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (symbol P.1).support)
    (hey : ∀ d ∈ (symbol P.1).support, d 1 ≤ e 1)
    (hex : ∀ d ∈ (symbol P.1).support, d 1 = e 1 → d 0 ≤ e 0)
    (hnegative : grade e < 0) : 10 ≤ mass P.1 := by
  obtain ⟨σ,hσ,hface,haxis⟩ := preliminary_axis_diagonal_positive_face
    hsource P Q hpair n hmem hunique
  obtain ⟨lam,α,a,b,hlam,hα,hb,hd,hf⟩ :=
    preliminary_positive_face_binomial hsource P Q hpair σ hσ hface
  exact preliminary_positive_binomial_mass_of_negative_top_boundary hsource hdegree
    P Q hpair σ a b hσ (by omega) lam α hlam hα hd hf e he hey hex hnegative

end Dixmier.Weyl
