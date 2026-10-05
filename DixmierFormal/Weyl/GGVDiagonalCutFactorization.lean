/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalRootBudget
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Factorization of the diagonal cut with at most two distinct roots

The complete complex root product retains arbitrary multiplicities. Applied
to the actual diagonal cut, it gives the scalar shapes needed for homogeneous
reconstruction of the case classification.
-/
namespace Dixmier.Weyl
open Polynomial

/-- A nonzero complex polynomial with at most two distinct roots has
one of the complete root-product shapes, with positive multiplicities. -/
theorem complex_polynomial_two_root_factorization
    (p : ℂ[X]) (hp : p ≠ 0) (hcard : p.roots.toFinset.card ≤ 2) :
    (∃ lam : ℂ, lam ≠ 0 ∧ p = C lam) ∨
    (∃ (lam α : ℂ) (k : ℕ), lam ≠ 0 ∧ 1 ≤ k ∧ p = C lam * (X-C α)^k) ∨
    (∃ (lam α β : ℂ) (u v : ℕ), lam ≠ 0 ∧ α ≠ β ∧ 1 ≤ u ∧ 1 ≤ v ∧
      p = C lam * (X-C α)^u * (X-C β)^v) := by
  classical
  have hlam : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  rw [prod_multiset_root_eq_finset_root] at hprod
  have hmult : ∀ α ∈ p.roots.toFinset, 1 ≤ rootMultiplicity α p := by
    intro α hα
    have hmem : α ∈ p.roots := Multiset.mem_toFinset.mp hα
    have hpos : 0 < rootMultiplicity α p := by
      rw [← count_roots]
      exact Multiset.count_pos.mpr hmem
    omega
  by_cases hzero : p.roots.toFinset.card = 0
  · have he := Finset.card_eq_zero.mp hzero
    exact Or.inl ⟨p.leadingCoeff, hlam, by simpa [he] using hprod⟩
  · by_cases hone : p.roots.toFinset.card = 1
    · obtain ⟨α, hset⟩ := Finset.card_eq_one.mp hone
      have hα : α ∈ p.roots.toFinset := by rw [hset]; simp
      exact Or.inr (Or.inl ⟨p.leadingCoeff, α, rootMultiplicity α p, hlam,
        hmult α hα, by simpa [hset] using hprod⟩)
    · have htwo : p.roots.toFinset.card = 2 := by omega
      obtain ⟨α, β, hne, hset⟩ := Finset.card_eq_two.mp htwo
      have hα : α ∈ p.roots.toFinset := by rw [hset]; simp
      have hβ : β ∈ p.roots.toFinset := by rw [hset]; simp
      refine Or.inr (Or.inr ⟨p.leadingCoeff, α, β, rootMultiplicity α p,
        rootMultiplicity β p, hlam, hne, hmult α hα, hmult β hβ, ?_⟩)
      simpa [hset, hne, mul_assoc] using hprod

/-- The actual diagonal cut of a counterexample is nonzero. -/
theorem counterexample_diagonal_cut_ne_zero
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) : cutPoly 1 1 P.1 ≠ 0 := by
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
    (by norm_num [IsDirection])
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr
    (leadingForm_ne_zero_of_vDeg_pos P 1 1 hp)
  obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective e
  have hw := (polynomialFace_point_source_data P 1 1 i j he).2
  have hcut := cutPoly_coeff_at_face_point P 1 1 i j (by norm_num) (by simpa using hw)
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp he
  rw [← hcut, hz] at hcoeff
  exact hcoeff (by simp)

/-- The preliminary companion supplies the complete scalar
zero-, one- or two-distinct-root factorization of the actual diagonal cut. -/
theorem preliminary_diagonal_cut_factorization
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    (∃ lam : ℂ, lam ≠ 0 ∧ cutPoly 1 1 P.1 = C lam) ∨
    (∃ (lam α : ℂ) (k : ℕ), lam ≠ 0 ∧ 1 ≤ k ∧
      cutPoly 1 1 P.1 = C lam * (X-C α)^k) ∨
    (∃ (lam α β : ℂ) (u v : ℕ), lam ≠ 0 ∧ α ≠ β ∧ 1 ≤ u ∧ 1 ≤ v ∧
      cutPoly 1 1 P.1 = C lam * (X-C α)^u * (X-C β)^v) := by
  exact complex_polynomial_two_root_factorization (cutPoly 1 1 P.1)
    (counterexample_diagonal_cut_ne_zero P Q hpair)
    (preliminary_diagonal_cut_distinct_roots_le_two hsource P Q hpair)

end Dixmier.Weyl
