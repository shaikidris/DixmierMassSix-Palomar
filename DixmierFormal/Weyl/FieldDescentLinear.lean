/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl

theorem exists_field_extension_retraction
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ∃ r : L →ₗ[K] K, ∀ a : K, r (algebraMap K L a) = a := by
  let i : K →ₗ[K] L := Algebra.linearMap K L
  have hi : LinearMap.ker i = ⊥ := LinearMap.ker_eq_bot.mpr
    (FaithfulSMul.algebraMap_injective K L)
  obtain ⟨r, hr⟩ := i.exists_leftInverse_of_injective hi
  refine ⟨r, ?_⟩
  intro a
  have := LinearMap.congr_fun hr a
  simpa [i] using this

theorem finite_linear_system_descends
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    {m n : Type*} [Fintype n] (A : m → n → K) (b : m → K)
    (h : ∃ x : n → L, ∀ i : m,
      (∑ j : n, algebraMap K L (A i j) * x j) = algebraMap K L (b i)) :
    ∃ y : n → K, ∀ i : m, (∑ j : n, A i j * y j) = b i := by
  obtain ⟨r, hr⟩ := exists_field_extension_retraction K L
  obtain ⟨x, hx⟩ := h
  refine ⟨fun j => r (x j), ?_⟩
  intro i
  have hh := congrArg r (hx i)
  simpa only [map_sum, ← Algebra.smul_def, map_smul, smul_eq_mul, hr] using hh

end Dixmier.Weyl
