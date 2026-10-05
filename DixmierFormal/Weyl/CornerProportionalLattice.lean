/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerAdjacentDivisibility

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Indivisibility of the normalized ramified corner

The lattice point `(h - 1/l, h)` is primitive in the ramified
coordinates `(i/l, j)`: any nonnegative-order lattice point on its
positive ray is an integer multiple of it. This is the arithmetic
step used in the proportional-companion branch of G13 Proposition 5.6.
-/

namespace Dixmier.Weyl

theorem ramified_corner_parallel_lattice_multiple
    (l h j : ℕ) (i : ℤ) (hh : 0 < h)
    (hparallel : i * (h : ℤ) =
      (j : ℤ) * ((l : ℤ) * (h : ℤ) - 1)) :
    ∃ μ : ℕ, j = μ * h ∧
      i = (μ : ℤ) * ((l : ℤ) * (h : ℤ) - 1) := by
  have hdivZ : (h : ℤ) ∣ (j : ℤ) := by
    refine ⟨(l : ℤ) * (j : ℤ) - i, ?_⟩
    nlinarith [hparallel]
  have hdiv : h ∣ j := by exact_mod_cast hdivZ
  obtain ⟨μ, hμ⟩ := hdiv
  refine ⟨μ, by simpa [Nat.mul_comm] using hμ, ?_⟩
  have hcancel : i * (h : ℤ) =
      ((μ : ℤ) * ((l : ℤ) * (h : ℤ) - 1)) * (h : ℤ) := by
    rw [hμ] at hparallel
    push_cast at hparallel
    nlinarith [hparallel]
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hh)) hcancel

/-- Source-coordinate version: the first coordinate is measured in
`X^(1/l)`, while the second is the derivative order. -/
theorem ramified_corner_rational_parallel_lattice_multiple
    (l h j : ℕ) (i : ℤ) (hl : 0 < l) (hh : 0 < h)
    (hparallel : ((i : ℚ) / (l : ℚ)) * (h : ℚ) =
      (j : ℚ) * ((h : ℚ) - 1 / (l : ℚ))) :
    ∃ μ : ℕ, j = μ * h ∧
      i = (μ : ℤ) * ((l : ℤ) * (h : ℤ) - 1) := by
  have hlQ : (l : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hparallelQ : (i : ℚ) * (h : ℚ) =
      (j : ℚ) * ((l : ℚ) * (h : ℚ) - 1) := by
    field_simp at hparallel ⊢
    nlinarith [hparallel]
  have hparallelZ : i * (h : ℤ) =
      (j : ℤ) * ((l : ℤ) * (h : ℤ) - 1) := by
    exact_mod_cast hparallelQ
  exact ramified_corner_parallel_lattice_multiple l h j i hh hparallelZ

end Dixmier.Weyl
