/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.Statements
public import DixmierFormal.Scalar.Classification

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Public scalar theorems

Each theorem proves one frozen statement of `DixmierFormal.Scalar.Statements` with no
hypotheses beyond those in the statement.  The imported Weyl-algebra inputs of the paper play no
role here: these results are unconditional.
-/

namespace Dixmier

open Polynomial

/-- Sparse multiplicity bound. -/
theorem sparseRootBound : Statement.SparseRootBound := by
  intro S α hS hα
  have := rootMultiplicity_lt_termCount hS hα
  omega

private theorem ne_zero_of_termCount_pos {S : ℂ[X]} (h : 0 < termCount S) : S ≠ 0 := by
  rintro rfl; simp [termCount] at h

/-- Uniqueness of a fourth-order root of a five-term polynomial with primitive support. -/
theorem fiveTermUniqueFourthOrderRoot : Statement.FiveTermUniqueFourthOrderRoot := by
  intro S h5 hprim α β _ hβ hα4 hβ4
  have hS : S ≠ 0 := ne_zero_of_termCount_pos (by omega)
  exact eq_of_five_terms h5 hprim.1 (fun ζ hζ => eq_one_of_forall_pow_eq_one hprim hζ) hβ
    ((le_rootMultiplicity_iff hS).mp hα4) ((le_rootMultiplicity_iff hS).mp hβ4)

/-- Two fourth-order roots of a six-term polynomial with primitive support. -/
theorem sixTermTwoFourthOrderRoots : Statement.SixTermTwoFourthOrderRoots := by
  intro S α β h6 h1 hprim hα _ hαβ hα4 hβ4
  have hS : S ≠ 0 := ne_zero_of_termCount_pos (by omega)
  obtain ⟨huniq, hreal⟩ := six_term_two_roots h6 h1
    (fun ζ hζ => eq_one_of_forall_pow_eq_one hprim hζ) hα hαβ
    ((le_rootMultiplicity_iff hS).mp hα4) ((le_rootMultiplicity_iff hS).mp hβ4)
  exact ⟨fun γ _ hγ4 => huniq γ ((le_rootMultiplicity_iff hS).mp hγ4), hreal⟩

/-- The scalar classification. -/
theorem scalarClassification : Statement.ScalarClassification := by
  intro ρ s r f hs hsρ hr hr0 hE ht
  lift s to ℕ using (by omega)
  lift ρ to ℕ using (by omega)
  have h : Comp ρ s r f := (companionEq_natCast_iff ρ s r f).mp hE
  obtain ⟨h1, h2, h3⟩ := h.classification (by exact_mod_cast hs) (by exact_mod_cast hsρ) hr hr0 ht
  exact ⟨by exact_mod_cast h1, h2, h3⟩

end Dixmier
