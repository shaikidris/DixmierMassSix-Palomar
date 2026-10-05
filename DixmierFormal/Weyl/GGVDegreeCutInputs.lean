/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPolynomialCornerProved

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Degree and ramified cut obligations for mass-six generation

The polynomial corner, homogeneous companion and opposite-grade results
are proved internally. The two fields below retain the exact outstanding
source contracts needed for the characteristic-zero generation theorem.
-/

namespace Dixmier.Weyl

structure GGVDegreeCutInputs : Prop where
  degreeBound : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
    15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)
  cutCorner : ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (u v₀ n d h : ℕ), IsCounterexamplePair P Q →
    IsDirection ρ σ → 0 < ρ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
    0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 → ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1 →
    ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
    (∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) →
    (∃ e ∈ (leadingForm ρ σ Q.1).support, grade e < 0) →
    expo u v₀ ∈ (leadingForm ρ σ P.1).support →
    (∀ e ∈ (leadingForm ρ σ P.1).support, grade e ≤ grade (expo u v₀)) →
    vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
    ¬ (((u : ℚ) + ((v₀ : ℚ) - maxRootMult (cutPoly ρ σ P.1)) * σ / ρ) / d = h - 1 / ρ ∧
        (maxRootMult (cutPoly ρ σ P.1) : ℚ) / d = h)

theorem ggvGeometricInputs_of_degree_cut (H : GGVDegreeCutInputs) :
    GGVGeometricRemainingInputs :=
  { degreeBound := H.degreeBound
    cutCorner := H.cutCorner
    corner := ggv_polynomial_corner_proved }

theorem ggvInputs_of_degree_cut (H : GGVDegreeCutInputs) : GGVInputs :=
  ggvInputs_of_geometric (ggvGeometricInputs_of_degree_cut H)

/-- Full arbitrary-characteristic-zero-field mass-six generation, conditional
only on the degree-gcd and ramified cut-corner contracts. -/
theorem massSixGeneration_of_degree_cut (H : GGVDegreeCutInputs) :
    Statement.MassSixGeneration :=
  massSixGeneration_of_GGV (ggvInputs_of_degree_cut H)

end Dixmier.Weyl
