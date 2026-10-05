module

public import DixmierFormal.Weyl.GGVRemainingInputs
public import DixmierFormal.Weyl.GGVCompanionJosephFrontier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Three remaining geometric source premises

Opposite grades and the full homogeneous companion are proved internally.
The case alternative follows from the companion and degree bound. The
remaining inputs are the degree-gcd bound and the two corner exclusions.
-/
namespace Dixmier.Weyl
open MvPolynomial

structure GGVGeometricRemainingInputs : Prop where
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

 theorem ggvRemainingInputs_of_geometric (H : GGVGeometricRemainingInputs) : GGVRemainingInputs :=
  { companion := ggv_companion_proved
    degreeBound := H.degreeBound
    cutCorner := H.cutCorner
    corner := H.corner }

 theorem ggvInputs_of_geometric (H : GGVGeometricRemainingInputs) : GGVInputs :=
  ggvInputs_of_remaining (ggvRemainingInputs_of_geometric H)

 theorem massSixGeneration_of_geometric_GGV (H : GGVGeometricRemainingInputs) :
    Statement.MassSixGeneration :=
  massSixGeneration_of_GGV (ggvInputs_of_geometric H)

end Dixmier.Weyl
