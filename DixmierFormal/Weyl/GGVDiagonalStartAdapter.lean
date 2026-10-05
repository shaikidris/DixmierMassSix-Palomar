/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCompanionAdapter
public import DixmierFormal.Weyl.PoissonDiagonalStart

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Diagonal-start consequence of the preliminary companion

The polynomial Poisson obstruction is applied to the actual leading symbol
of a counterexample pair. The only imported source premise is the G13
preliminary companion itself; this file does not prove that premise.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- A G13 preliminary companion excludes a nonconstant diagonal exponent
as the maximal-grade point of an actual leading face. -/
theorem ggv_preliminary_no_diagonal_leading_top
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    {d : Fin 2 →₀ ℕ}
    (hd : d ∈ (leadingForm ρ σ P.1).support)
    (hdmax : ∀ x ∈ (leadingForm ρ σ P.1).support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hdiag : d 0 = d 1) (hdpos : 0 < d 0) : False := by
  obtain ⟨F, hFhom, hcomp⟩ := hsource P Q hpair ρ σ hdir
  have hRhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  exact poisson_companion_no_diagonal_homogeneous_max ρ σ
    (vDeg ρ σ P.1) (ρ + σ) (ne_of_gt hdir.2)
    (leadingForm ρ σ P.1) F hRhom hFhom hcomp
    hd hdmax hdiag hdpos

/-- The same consequence with G13's preliminary companion retained in its
operator/PBW form until the symbol translation. -/
theorem ggv_operator_preliminary_no_diagonal_leading_top
    (hsource : GGVOperatorPreliminaryInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    {d : Fin 2 →₀ ℕ}
    (hd : d ∈ (leadingForm ρ σ P.1).support)
    (hdmax : ∀ x ∈ (leadingForm ρ σ P.1).support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hdiag : d 0 = d 1) (hdpos : 0 < d 0) : False :=
  ggv_preliminary_no_diagonal_leading_top
    (ggv_preliminary_companion_of_operator_input hsource)
    P Q hpair ρ σ hdir hd hdmax hdiag hdpos

end Dixmier.Weyl
