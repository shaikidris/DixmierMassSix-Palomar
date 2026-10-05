module

public import DixmierFormal.Weyl.GGVCaseFieldAdapter
public import DixmierFormal.Weyl.FieldArbitraryGeneration
public import DixmierFormal.Weyl.OneSidedScalarNormalize

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Four independent structural premises

The mass-six generation theorem needs these four source premises. Opposite
 grades are proved internally; the case alternative is derived from the
 companion and degree premises. The public GGVInputs contract is preserved.
-/
namespace Dixmier.Weyl
open MvPolynomial

/-- Independent structural premises for mass-six generation. -/
structure GGVRemainingInputs : Prop where
  companion : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
    ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
      μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
      IsWeightedHomogeneous (wt ρ σ) F (ρ + σ) ∧
      leadingForm ρ σ P.1 = C μ * R ^ k ∧ poisson R F = R
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
  corner : ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ), IsCounterexamplePair P Q →
    IsDirection ρ σ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
    0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 →
    ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
    expo a b ∈ (leadingForm ρ σ P.1).support →
    (∀ e ∈ (leadingForm ρ σ P.1).support, grade (expo a b) ≤ grade e) →
    vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
    ¬ ((a : ℚ) / d = h - 1 ∧ (b : ℚ) / d = h)

/-- Assemble the public contract using the proved grade and derived case fields. -/
def ggvInputs_of_remaining (H : GGVRemainingInputs) : GGVInputs where
  grades_opposite := ggv_grades_opposite_proved
  companion := H.companion
  caseSplit := ggv_caseSplit_of_companion_degree_fields H.companion H.degreeBound
  degreeBound := H.degreeBound
  cutCorner := H.cutCorner
  corner := H.corner

/-- Mass-six generation over every characteristic-zero field from the four
 independent structural source premises, with unrestricted mate. -/
theorem massSixGeneration_of_remaining_GGV (H : GGVRemainingInputs) :
    Statement.MassSixGeneration :=
  massSixGeneration_of_GGV (ggvInputs_of_remaining H)

end Dixmier.Weyl
