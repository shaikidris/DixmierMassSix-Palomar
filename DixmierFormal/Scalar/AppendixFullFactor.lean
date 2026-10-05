/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixFactorization

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Squarefree and coprime factors in Appendix A

The normalized root-product factors are squarefree and pairwise coprime
because the exact companion polynomial is separable. This completes the
factorization clause of Proposition A.1 under its maximum-multiplicity
hypothesis. The positive-degree connection for `B` and the bundled
Proposition A.1 theorem remain separate.
-/

namespace Dixmier
open Polynomial

/-- The normalized factorization with squarefree, pairwise coprime factors. -/
theorem appendix_full_factorization {ρ s : ℕ} {r f : ℂ[X]}
    (h : Comp ρ s r f) (hsρ : s < ρ) (hr0 : r.eval 0 = 1)
    (hq : ∀ γ : ℂ, rootMultiplicity γ r ≤ 2) :
    ∃ A B Cc : ℂ[X],
      A.eval 0 = 1 ∧ B.eval 0 = 1 ∧ Cc.eval 0 = -1 ∧
      Squarefree A ∧ Squarefree B ∧ Squarefree Cc ∧
      IsCoprime A B ∧ IsCoprime A Cc ∧ IsCoprime B Cc ∧
      r = A*B^2 ∧ f = A*B*Cc := by
  obtain ⟨A,B,Cc,hA0,hB0,hC0,hr,hf⟩ :=
    appendix_normalized_factorization h hsρ hr0 hq
  have hsep := h.companion_separable hsρ hr0
  have hA_dvd : A ∣ f := by
    refine ⟨B*Cc, ?_⟩
    simpa [mul_assoc] using hf
  have hB_dvd : B ∣ f := by
    refine ⟨A*Cc, ?_⟩
    calc f = A*B*Cc := hf
      _ = B*(A*Cc) := by ring
  have hC_dvd : Cc ∣ f := by
    refine ⟨A*B, ?_⟩
    calc f = A*B*Cc := hf
      _ = Cc*(A*B) := by ring
  have hAB_dvd : A*B ∣ f := by
    refine ⟨Cc, ?_⟩
    simpa [mul_assoc] using hf
  have hAC_dvd : A*Cc ∣ f := by
    refine ⟨B, ?_⟩
    calc f = A*B*Cc := hf
      _ = (A*Cc)*B := by ring
  have hBC_dvd : B*Cc ∣ f := by
    refine ⟨A, ?_⟩
    calc f = A*B*Cc := hf
      _ = (B*Cc)*A := by ring
  refine ⟨A,B,Cc,hA0,hB0,hC0,?_,?_,?_,?_,?_,?_,hr,hf⟩
  · exact (hsep.of_dvd hA_dvd).squarefree
  · exact (hsep.of_dvd hB_dvd).squarefree
  · exact (hsep.of_dvd hC_dvd).squarefree
  · exact (hsep.of_dvd hAB_dvd).isCoprime
  · exact (hsep.of_dvd hAC_dvd).isCoprime
  · exact (hsep.of_dvd hBC_dvd).isCoprime

end Dixmier
