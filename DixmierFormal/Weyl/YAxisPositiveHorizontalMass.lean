/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.AxisNegativeTopMass
public import DixmierFormal.Weyl.FourierBoundaryOccupancy

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Y-axis diagonal with a positive horizontal endpoint

Fourier transports the exact occupied endpoint to the negative highest-row
boundary required by the positive-face mass estimate.
-/
namespace Dixmier.Weyl

/-- The original Y-axis diagonal branch with positive horizontal endpoint
has mass at least ten. The source companion and degree inputs remain explicit. -/
theorem preliminary_y_axis_positive_horizontal_mass_ge_ten
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (n a b : ℕ) (hdiag : totalDeg P.1 = n)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo 0 n)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ a)
    (hy : ∀ d ∈ (symbol P.1).support, d 0 = a → d 1 ≤ b)
    (hpositive : b < a) : 10 ≤ mass P.1 := by
  have hn : 0 < n := by have ht := hdegree P Q hpair; rw [hdiag] at ht; omega
  obtain ⟨hFmem,hFunique⟩ := fourier_diagonal_face_unique P 0 n
    (by simpa using hdiag) (by omega) hunique
  have hFpoint := fourier_rightmost_column_endpoint_mem P a b (by omega) hpoint hx hy
  obtain ⟨hFy,hFx⟩ := fourier_rightmost_column_boundary_bounds P a b hx hy
  have hmass := preliminary_axis_diagonal_negative_top_mass_ge_ten hsource hdegree
    (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) (isCounterexamplePair_fourier P Q hpair) n
    hFmem hFunique (expo b a) hFpoint
    (by simpa [expo] using hFy)
    (by simpa [expo] using hFx)
    (by simp [grade,expo]; omega)
  simpa only [mass_fourierAlgHom] using hmass

/-- The positive-horizontal Y-axis branch supplies the original member's
mass alternative in the frozen case map. -/
theorem preliminary_y_axis_positive_horizontal_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (n a b : ℕ) (hdiag : totalDeg P.1 = n)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo 0 n)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hx : ∀ d ∈ (symbol P.1).support, d 0 ≤ a)
    (hy : ∀ d ∈ (symbol P.1).support, d 0 = a → d 1 ≤ b)
    (hpositive : b < a) : CaseAlternative P.1 := by
  exact Or.inr (Or.inl (preliminary_y_axis_positive_horizontal_mass_ge_ten hsource hdegree
    P Q hpair n a b hdiag hunique hpoint hx hy hpositive))

end Dixmier.Weyl
