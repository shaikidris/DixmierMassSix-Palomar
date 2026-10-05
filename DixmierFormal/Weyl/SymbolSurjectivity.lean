/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Fourier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Every polynomial symbol has a finite Weyl normal ordering

This is the polynomial (unramified) symbol-to-operator half of the G13
homogeneous-companion transfer. Multiplication is intentionally not
preserved by the PBW symbol map.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

theorem symbolLinearMap_surjective
    {K : Type*} [Field K] [CharZero K] :
    Function.Surjective (symbolLinearMap (K := K)) := by
  intro S
  induction S using MvPolynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      refine ⟨P+Q, ?_⟩
      rw [map_add, hP, hQ]
  | monomial d c =>
      obtain ⟨⟨i,j⟩, hd⟩ := expo_surjective d
      change expo i j = d at hd
      refine ⟨c • ((concreteX K)^i * (concreteY K)^j), ?_⟩
      rw [map_smul]
      change c • symbol (((concreteX K)^i * (concreteY K)^j : A1 K) :
        Module.End K K[X]) = _
      rw [symbol_concreteNormalMonomial, hd]
      simp [MvPolynomial.smul_monomial]

/-- A nonzero homogeneous commutative companion has an actual finite
Weyl operator with exactly that symbol and the same Newton degree. -/
theorem weightedHomogeneous_symbol_has_operator
    (F : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hF : F.IsWeightedHomogeneous (wt ρ σ) m)
    (hFne : F ≠ 0) :
    ∃ T : A1 ℂ, symbol T.1 = F ∧ vDeg ρ σ T.1 = m := by
  obtain ⟨T, hT⟩ := symbolLinearMap_surjective F
  have hsymbol : symbol T.1 = F := hT
  have hdeg : MvPolynomial.weightedTotalDegree' (wt ρ σ) F =
      (m : WithBot ℤ) := by
    apply le_antisymm
    · simp only [MvPolynomial.weightedTotalDegree', Finset.sup_le_iff]
      intro d hd
      exact_mod_cast le_of_eq (hF (MvPolynomial.mem_support_iff.mp hd))
    · obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hFne
      rw [← hF hd]
      exact Finset.le_sup (f := fun e =>
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
        (MvPolynomial.mem_support_iff.mpr hd)
  refine ⟨T, hsymbol, ?_⟩
  rw [vDeg, hsymbol, hdeg]
  rfl

end Dixmier.Weyl
