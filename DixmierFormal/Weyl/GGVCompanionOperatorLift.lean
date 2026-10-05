/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.SymbolSurjectivity
public import DixmierFormal.Weyl.GGVCompanionAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Lifting a polynomial Poisson companion to a Weyl operator

The PBW symbol is surjective as a linear map. For a nonzero homogeneous
companion, its normal-ordered lift has the same Newton weight, and the
first commutator component is the prescribed Poisson bracket.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

private theorem symbol_degree_eq_vDeg_of_pos
    (T : A1 ℂ) (ρ σ : ℤ) (hpos : 0 < vDeg ρ σ T.1) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T.1) =
      (vDeg ρ σ T.1 : WithBot ℤ) := by
  cases h : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T.1) with
  | bot => simp [vDeg, h] at hpos
  | coe m => simp [vDeg, h]

theorem ggv_operator_preliminary_of_symbol_input
    (hsource : GGVPreliminaryCompanionInput) :
    GGVOperatorPreliminaryInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨F, hFhom, hfixed⟩ := hsource P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hPne := leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos
  have hFne : F ≠ 0 := by
    intro hz
    rw [hz] at hfixed
    simp [poisson] at hfixed
    exact hPne hfixed.symm
  obtain ⟨T, hsymbol, hTdeg⟩ :=
    weightedHomogeneous_symbol_has_operator F ρ σ (ρ+σ) hFhom hFne
  have hTpos : 0 < vDeg ρ σ T.1 := by
    have hsum := hdir.2
    omega
  have htop := symbol_commutator_top_component P T ρ σ
    (vDeg ρ σ P.1) (vDeg ρ σ T.1) hdir.2
    (symbol_degree_eq_vDeg_of_pos P ρ σ hPpos)
    (symbol_degree_eq_vDeg_of_pos T ρ σ hTpos)
  rw [hTdeg, hsymbol,
    MvPolynomial.weightedHomogeneousComponent_eq_self
      (w := wt ρ σ) hFhom] at htop
  have hindex : vDeg ρ σ P.1 + (ρ+σ) - (ρ+σ) =
      vDeg ρ σ P.1 := by omega
  rw [hindex] at htop
  refine ⟨T, hTdeg, hsymbol ▸ hFhom, ?_⟩
  simpa [hTdeg] using htop.trans hfixed

theorem ggv_operator_preliminary_iff_symbol :
    GGVOperatorPreliminaryInput ↔ GGVPreliminaryCompanionInput :=
  ⟨ggv_preliminary_companion_of_operator_input,
    ggv_operator_preliminary_of_symbol_input⟩

end Dixmier.Weyl
