/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingScalarBridge
public import DixmierFormal.Scalar.GeneralRootDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! Root-multiplicity consequences of the general strict-crossing equation. -/

namespace Dixmier.Weyl
open Polynomial

/-- In a strict negative crossing, one root of the base polynomial has
multiplicity greater than the initial `x` exponent. No mass bound is used. -/
theorem crossing_exists_rootMultiplicity_gt_a
    (ρ s a b : ℕ) (r f : ℂ[X])
    (hs : 0 < s) (hsρ : s < ρ) (hab : b < a)
    (hr0 : r.coeff 0 = 1) (hr : 0 < r.natDegree)
    (h : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r) = 0) :
    ∃ α : ℂ, r.IsRoot α ∧ a < rootMultiplicity α r ∧
      ∀ β : ℂ, r.IsRoot β → rootMultiplicity β r ≤ rootMultiplicity α r := by
  obtain ⟨hf, _hlt, hid, hroots⟩ :=
    crossing_general_scalar_facts ρ s a b r f hsρ hab hr0 hr h
  obtain ⟨α, hα, hmax⟩ := Dixmier.General.exists_max_rootMultiplicity r hr
  have he : r.natDegree ≤ rootMultiplicity α r * f.natDegree :=
    Dixmier.General.degree_le_maxMultiplicity_mul_companionDegree r f
      (rootMultiplicity α r) (ne_zero_of_natDegree_gt hr)
      (ne_zero_of_natDegree_gt hf) (fun β hβ => (hroots β hβ).1) hmax
  exact ⟨α, hα,
    crossing_maxMultiplicity_gt_a ρ s a b r.natDegree f.natDegree
      (rootMultiplicity α r) hs hsρ hab hf hid he, hmax⟩

end Dixmier.Weyl
