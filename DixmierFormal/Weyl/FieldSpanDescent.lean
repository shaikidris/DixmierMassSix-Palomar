/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FieldBaseChangePBW
public import DixmierFormal.Weyl.FieldDescentLinear

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl
open Polynomial
noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [CharZero K]

private theorem pbwCoeff_finset_sum {ι : Type*} (s : Finset ι) (v : ι → A1 K)
    (i j : ℕ) :
    pbwCoeff ((∑ t ∈ s, v t : A1 K) : Module.End K K[X]) i j =
      ∑ t ∈ s, pbwCoeff ((v t : A1 K) : Module.End K K[X]) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pbwCoeff, coeffPoly]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    change pbwCoeff ((v a : Module.End K K[X]) +
      ((∑ t ∈ s, v t : A1 K) : Module.End K K[X])) i j = _
    rw [pbwCoeff_add, ih]

/-- A finite linear dependence of extended Weyl operators with a source-field target
already has coefficients in the source field. -/
theorem finite_weyl_span_descends {ι : Type*} [Fintype ι]
    (v : ι → A1 K) (T : A1 K)
    (h : ∃ a : ι → L,
      (∑ t, a t • concreteBaseChange K L (v t)) = concreteBaseChange K L T) :
    ∃ b : ι → K, (∑ t, b t • v t) = T := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective K L)
  obtain ⟨r, hr⟩ := exists_field_extension_retraction K L
  obtain ⟨a, ha⟩ := h
  refine ⟨fun t => r (a t), ?_⟩
  apply symbol_injective
  apply MvPolynomial.ext
  intro p
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective p
  rw [symbol_coeff_pbwCoeff, symbol_coeff_pbwCoeff]
  have hc := congrArg (fun U : A1 L =>
    pbwCoeff (U : Module.End L L[X]) i j) ha
  simp only [pbwCoeff_finset_sum, SetLike.val_smul, pbwCoeff_smul,
    pbwCoeff_concreteBaseChange] at hc ⊢
  have hrc := congrArg r hc
  have hterm (t : ι) :
      r (a t * algebraMap K L (pbwCoeff (v t : Module.End K K[X]) i j)) =
        r (a t) * pbwCoeff (v t : Module.End K K[X]) i j := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simpa only [map_sum, hterm, hr] using hrc

end
end Dixmier.Weyl
