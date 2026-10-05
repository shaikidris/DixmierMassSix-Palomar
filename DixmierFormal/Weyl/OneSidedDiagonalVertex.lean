/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedSupportGeometry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Maximal diagonal support points are exposed vertices

For a finite support contained in nonpositive grades, a sufficiently small
positive perturbation of the grade direction exposes its maximal positive
diagonal point. The integer normal `(N,1-N)` is explicit.
-/

namespace Dixmier.Weyl

def diagonalVertexWeight (N : ℕ) (p : ℕ × ℕ) : ℤ :=
  (N : ℤ) * p.1 + (1 - (N : ℤ)) * p.2

/-- Every normal with parameter above all second coordinates exposes the
maximal diagonal point. The universal parameter permits one normal to be
chosen for both members of an exact pair. -/
theorem oneSided_maximal_diagonal_exposed_of_bound (S : Finset (ℕ × ℕ))
    (hside : ∀ q ∈ S, q.1 ≤ q.2)
    (p : ℕ × ℕ) (_hp : p ∈ S) (hpdiag : p.1 = p.2)
    (hmax : ∀ q ∈ S, q.1 = q.2 → q.2 ≤ p.2)
    (N : ℕ) (hbound : ∀ q ∈ S, q.2 < N) :
    ∀ q ∈ S, q ≠ p → diagonalVertexWeight N q < diagonalVertexWeight N p := by
  intro q hq hneq
  have hqbound : q.2 < N := hbound q hq
  have hqside := hside q hq
  by_cases hqdiag : q.1 = q.2
  · have hqm := hmax q hq hqdiag
    have hstrict : q.2 < p.2 := by
      by_contra hn
      have heq : q.2 = p.2 := by omega
      apply hneq
      exact Prod.ext (by omega) heq
    dsimp [diagonalVertexWeight]
    have hqz : (q.2 : ℤ) < p.2 := by exact_mod_cast hstrict
    rw [hqdiag, hpdiag]
    convert hqz using 1 <;> ring
  · have hgap : q.1 + 1 ≤ q.2 := by omega
    have hNz : (q.2 : ℤ) < N := by exact_mod_cast hqbound
    have hgapz : (q.1 : ℤ) + 1 ≤ q.2 := by exact_mod_cast hgap
    have hpnonneg : 0 ≤ (p.2 : ℤ) := by positivity
    have hNz : 0 ≤ (N : ℤ) := by positivity
    have hdiff : (q.1 : ℤ) - q.2 ≤ -1 := by omega
    have hmul : (N : ℤ) * ((q.1 : ℤ) - q.2) ≤ -(N : ℤ) := by
      have hh := mul_le_mul_of_nonneg_left hdiff hNz
      nlinarith
    dsimp [diagonalVertexWeight]
    rw [hpdiag]
    nlinarith [hmul]

/-- A maximal diagonal point in a finite one-sided support is exposed by a
primitive positive-sum integer direction. -/
theorem oneSided_maximal_diagonal_exposed (S : Finset (ℕ × ℕ))
    (hside : ∀ q ∈ S, q.1 ≤ q.2)
    (p : ℕ × ℕ) (hp : p ∈ S) (hpdiag : p.1 = p.2)
    (hmax : ∀ q ∈ S, q.1 = q.2 → q.2 ≤ p.2) :
    ∃ N : ℕ, 0 < N ∧
      ∀ q ∈ S, q ≠ p → diagonalVertexWeight N q < diagonalVertexWeight N p := by
  let M := S.sup' ⟨p, hp⟩ Prod.snd
  let N := M + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hbound : ∀ q ∈ S, q.2 < N := by
    intro q hq
    have hle : q.2 ≤ M := Finset.le_sup' Prod.snd hq
    dsimp [N]
    omega
  exact ⟨N, hN, oneSided_maximal_diagonal_exposed_of_bound S hside p hp hpdiag hmax N hbound⟩

/-- Once the normal parameter exceeds all second coordinates, every
maximizer has positive grade whenever the finite support contains any
positive-grade point. -/
theorem positive_grade_at_diagonal_normal_max (S : Finset (ℕ × ℕ))
    (N : ℕ) (hbound : ∀ q ∈ S, q.2 < N)
    (hpositive : ∃ q ∈ S, q.2 < q.1) :
    ∃ p ∈ S, p.2 < p.1 ∧
      ∀ q ∈ S, diagonalVertexWeight N q ≤ diagonalVertexWeight N p := by
  obtain ⟨q₀, hq₀, hpos⟩ := hpositive
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image (diagonalVertexWeight N) ⟨q₀, hq₀⟩
  refine ⟨p, hp, ?_, hmax⟩
  by_contra hn
  have hple : p.1 ≤ p.2 := by omega
  have hpbound := hbound p hp
  have hqgap : (q₀.2 : ℤ) + 1 ≤ q₀.1 := by exact_mod_cast hpos
  have hpgap : (p.1 : ℤ) ≤ p.2 := by exact_mod_cast hple
  have hpNz : (p.2 : ℤ) < N := by exact_mod_cast hpbound
  have hNnonneg : 0 ≤ (N : ℤ) := by positivity
  have hqmul : (N : ℤ) ≤ (N : ℤ) * ((q₀.1 : ℤ) - q₀.2) := by
    have hh : (1 : ℤ) ≤ (q₀.1 : ℤ) - q₀.2 := by omega
    have hm := mul_le_mul_of_nonneg_left hh hNnonneg
    nlinarith
  have hpmul : (N : ℤ) * ((p.1 : ℤ) - p.2) ≤ 0 := by
    have hh : (p.1 : ℤ) - p.2 ≤ 0 := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos hNnonneg hh
    exact hm
  have hqweight : (N : ℤ) ≤ diagonalVertexWeight N q₀ := by
    dsimp [diagonalVertexWeight]
    have hqnonneg : 0 ≤ (q₀.2 : ℤ) := by positivity
    nlinarith [hqmul]
  have hpweight : diagonalVertexWeight N p < N := by
    dsimp [diagonalVertexWeight]
    nlinarith [hpmul]
  have hcomp := hmax q₀ hq₀
  omega

end Dixmier.Weyl
