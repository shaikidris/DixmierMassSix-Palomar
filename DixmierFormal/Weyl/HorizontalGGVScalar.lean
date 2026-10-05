/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalNativeShape

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal scalar equation from the GGV companion input

The actual source-supplied homogeneous base and companion have horizontal
shapes. Their Poisson identity gives the precise scalar companion equation.
The theorem remains conditional on the explicit GGVInputs field.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem horizontal_counterexample_scalar_of_GGV
    (H : GGVInputs) (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    ∃ (μ : ℂ) (k a : ℕ) (g f : ℂ[X]),
      μ ≠ 0 ∧ 2 ≤ k ∧ g ≠ 0 ∧
      leadingForm 1 0 P.1 = MvPolynomial.C μ *
        (MvPolynomial.X 0 ^ a *
          g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ k ∧
      Dixmier.Horizontal.HorizComp a g f := by
  have hdir : IsDirection 1 0 := by norm_num [IsDirection]
  obtain ⟨μ, k, R, F, m, hμ, hk, hR, hRhom, hFhom, hface, hpoisson⟩ :=
    H.companion P Q hpair 1 0 hdir
  obtain ⟨a, U, _, hU, hRshape⟩ :=
    horizontal_nonzero_homogeneous_shape R m hR hRhom
  obtain ⟨V, hFshape⟩ :=
    horizontal_homogeneous_shape F 1 (by simpa using hFhom)
  simp only [pow_one] at hFshape
  let E := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  let g : ℂ[X] := E U
  let f : ℂ[X] := E V
  have hg : g ≠ 0 := E.map_ne_zero_iff.mpr hU
  have hbr' : poisson
      (MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ U)
      (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ V) =
      MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ U := by
    rw [← hRshape, ← hFshape]
    exact hpoisson
  have hscalar : Dixmier.Horizontal.HorizComp a g f :=
    horizontal_poisson_implies_scalar U V a hbr'
  refine ⟨μ, k, a, g, f, hμ, hk, hg, ?_, hscalar⟩
  rw [hface, hRshape]
  rw [horizontal_rename_eq_eval U]

end Dixmier.Weyl
