/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite one-sided support geometry

This is the combinatorial source of the two nonmonomial cases in Han--Tan's
one-sided argument. Coordinates are the project's PBW coordinates `(X-power,Y-power)`.
The distinguished derivative generator is `(0,1)`.
-/

namespace Dixmier.Weyl

def oneSidedRatio (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / ((p.2 : ℚ) - 1)

/-- Every point strictly below the grade diagonal other than `(0,1)` has a defined
ratio in `[0,1]`. Equality to one is exactly the grade-minus-one case. -/
theorem oneSidedRatio_bounds (p : ℕ × ℕ)
    (hgrade : p.1 < p.2) (hne : p ≠ (0, 1)) :
    0 ≤ oneSidedRatio p ∧ oneSidedRatio p ≤ 1 := by
  have hden : 0 < (p.2 : ℚ) - 1 := by
    have hj : 1 < p.2 := by
      by_contra h
      have hj' : p.2 ≤ 1 := by omega
      have hi : p.1 = 0 := by omega
      have hj'' : p.2 = 1 := by omega
      exact hne (Prod.ext hi hj'')
    have hjq : (1 : ℚ) < p.2 := by exact_mod_cast hj
    linarith

  constructor
  · exact div_nonneg (by positivity) hden.le
  · apply (div_le_iff₀ hden).2
    have h : p.1 + 1 ≤ p.2 := by omega
    have hq : (p.1 : ℚ) + 1 ≤ p.2 := by exact_mod_cast h
    linarith

/-- The endpoint ratio is one precisely for an additional point in grade `-1`. -/
theorem oneSidedRatio_eq_one_iff (p : ℕ × ℕ)
    (hgrade : p.1 < p.2) (hne : p ≠ (0, 1)) :
    oneSidedRatio p = 1 ↔ p.2 = p.1 + 1 := by
  have hden : (p.2 : ℚ) - 1 ≠ 0 := by
    have hj : 1 < p.2 := by
      by_contra hn
      have hle : p.2 ≤ 1 := by omega
      have hi : p.1 = 0 := by omega
      have hj' : p.2 = 1 := by omega
      exact hne (Prod.ext hi hj')
    have hjq : (1 : ℚ) < p.2 := by exact_mod_cast hj
    linarith
  constructor
  · intro h
    have hq : (p.1 : ℚ) = (p.2 : ℚ) - 1 := by
      have h' : (p.1 : ℚ) / ((p.2 : ℚ) - 1) = 1 := by
        simpa [oneSidedRatio] using h
      have := (div_eq_iff hden).mp h'
      linarith
    exact_mod_cast (show (p.2 : ℚ) = (p.1 : ℚ) + 1 by linarith)
  · intro h
    have hq : (p.2 : ℚ) - 1 = p.1 := by
      have h' : (p.2 : ℚ) = (p.1 : ℚ) + 1 := by exact_mod_cast h
      linarith
    have hi : p.1 ≠ 0 := by
      intro hz
      have hj : p.2 = 1 := by omega
      exact hne (Prod.ext hz hj)
    have hiq : (p.1 : ℚ) ≠ 0 := by exact_mod_cast hi
    simp [oneSidedRatio, hq, hiq]

/-- A nontrivial finite support strictly on one side of the diagonal has a
distinguished extremal point away from the derivative generator. The extremal
ratio lies in `[0,1]`; it selects the first face met when the normal rotates
from the horizontal direction to the grade direction. -/
theorem oneSidedSupport_extremal_ratio (S : Finset (ℕ × ℕ))
    (hgrade : ∀ p ∈ S, p.1 < p.2)
    (hother : ∃ p ∈ S, p ≠ (0, 1)) :
    ∃ p ∈ S, p ≠ (0, 1) ∧
      0 ≤ oneSidedRatio p ∧ oneSidedRatio p ≤ 1 ∧
      ∀ q ∈ S, q ≠ (0, 1) → oneSidedRatio q ≤ oneSidedRatio p := by
  classical
  have hne : (S.erase (0, 1)).Nonempty := by
    obtain ⟨p, hp, hpg⟩ := hother
    exact ⟨p, Finset.mem_erase.mpr ⟨hpg, hp⟩⟩
  obtain ⟨p, hp, hmax⟩ :=
    (S.erase (0, 1)).exists_max_image oneSidedRatio hne
  have hpmem := Finset.mem_erase.mp hp
  obtain ⟨hpg, hpS⟩ := hpmem
  obtain ⟨hlo, hhi⟩ := oneSidedRatio_bounds p (hgrade p hpS) hpg
  refine ⟨p, hpS, hpg, hlo, hhi, ?_⟩
  intro q hq hqg
  exact hmax q (Finset.mem_erase.mpr ⟨hqg, hq⟩)

/-- The extremal line is either the grade `-1` boundary or has strictly
positive coordinate sum. In the latter case the finite support contains no
second grade-`-1` point. -/
theorem oneSidedSupport_ratio_dichotomy (S : Finset (ℕ × ℕ))
    (hgrade : ∀ p ∈ S, p.1 < p.2)
    (hother : ∃ p ∈ S, p ≠ (0, 1)) :
    (∃ p ∈ S, p ≠ (0, 1) ∧ p.2 = p.1 + 1) ∨
    (∃ p ∈ S, p ≠ (0, 1) ∧ oneSidedRatio p < 1 ∧
      ∀ q ∈ S, q ≠ (0, 1) → oneSidedRatio q ≤ oneSidedRatio p) := by
  obtain ⟨p, hpS, hpg, _, hhi, hmax⟩ :=
    oneSidedSupport_extremal_ratio S hgrade hother
  by_cases hone : oneSidedRatio p = 1
  · exact Or.inl ⟨p, hpS, hpg, (oneSidedRatio_eq_one_iff p (hgrade p hpS) hpg).mp hone⟩
  · exact Or.inr ⟨p, hpS, hpg, lt_of_le_of_ne hhi hone, hmax⟩

/-- The extremal ratio exposes a face through the generator: every other
support point lies on or below its supporting line, and the selected point
lies on that line. This is the finite geometric dispatch before choosing a
primitive integer normal. -/
theorem oneSidedSupport_supporting_line (S : Finset (ℕ × ℕ))
    (hgrade : ∀ p ∈ S, p.1 < p.2)
    (hother : ∃ p ∈ S, p ≠ (0, 1)) :
    ∃ (t : ℚ) (p : ℕ × ℕ), p ∈ S ∧ p ≠ (0, 1) ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (p.1 : ℚ) = t * ((p.2 : ℚ) - 1) ∧
      ∀ q ∈ S, (q.1 : ℚ) ≤ t * ((q.2 : ℚ) - 1) := by
  obtain ⟨p, hpS, hpg, hlo, hhi, hmax⟩ :=
    oneSidedSupport_extremal_ratio S hgrade hother
  refine ⟨oneSidedRatio p, p, hpS, hpg, hlo, hhi, ?_, ?_⟩
  · have hden : (p.2 : ℚ) - 1 ≠ 0 := ne_of_gt (by
      have hj : 1 < p.2 := by
        have h := hgrade p hpS
        by_contra hn
        have hle : p.2 ≤ 1 := by omega
        have hi : p.1 = 0 := by omega
        have hj' : p.2 = 1 := by omega
        exact hpg (Prod.ext hi hj')
      have hjq : (1 : ℚ) < p.2 := by exact_mod_cast hj
      linarith)
    simp [oneSidedRatio, hden]
  · intro q hq
    by_cases hqg : q = (0, 1)
    · subst q
      simp
    · have hden : 0 < (q.2 : ℚ) - 1 := by
        have hj : 1 < q.2 := by
          have h := hgrade q hq
          by_contra hn
          have hle : q.2 ≤ 1 := by omega
          have hi : q.1 = 0 := by omega
          have hj' : q.2 = 1 := by omega
          exact hqg (Prod.ext hi hj')
        have hjq : (1 : ℚ) < q.2 := by exact_mod_cast hj
        linarith
      have hratio := hmax q hq hqg
      dsimp [oneSidedRatio] at hratio
      exact (div_le_iff₀ hden).mp hratio

/-- The selected line has a positive-sum normal unless a second support
point has grade `-1`. This is the exact finite dichotomy used before the
integer leading-form transfer. -/
theorem oneSidedSupport_face_dichotomy (S : Finset (ℕ × ℕ))
    (hgrade : ∀ p ∈ S, p.1 < p.2)
    (hother : ∃ p ∈ S, p ≠ (0, 1)) :
    (∃ p ∈ S, p ≠ (0, 1) ∧ p.2 = p.1 + 1) ∨
    (∃ (t : ℚ) (p : ℕ × ℕ), p ∈ S ∧ p ≠ (0, 1) ∧
      0 ≤ t ∧ t < 1 ∧
      (p.1 : ℚ) = t * ((p.2 : ℚ) - 1) ∧
      ∀ q ∈ S, (q.1 : ℚ) ≤ t * ((q.2 : ℚ) - 1)) := by
  obtain ⟨t, p, hpS, hpg, hlo, hhi, hpeq, hline⟩ :=
    oneSidedSupport_supporting_line S hgrade hother
  by_cases ht : t = 1
  · have hratio : oneSidedRatio p = 1 := by
      have hden : (p.2 : ℚ) - 1 ≠ 0 := by
        have hj : 1 < p.2 := by
          have h := hgrade p hpS
          by_contra hn
          have hle : p.2 ≤ 1 := by omega
          have hi : p.1 = 0 := by omega
          have hj' : p.2 = 1 := by omega
          exact hpg (Prod.ext hi hj')
        have hjq : (1 : ℚ) < p.2 := by exact_mod_cast hj
        linarith
      rw [ht] at hpeq
      simp only [one_mul] at hpeq
      simp [oneSidedRatio, hpeq, hden]
    exact Or.inl ⟨p, hpS, hpg, (oneSidedRatio_eq_one_iff p (hgrade p hpS) hpg).mp hratio⟩
  · exact Or.inr ⟨t, p, hpS, hpg, hlo, lt_of_le_of_ne hhi ht, hpeq, hline⟩

/-- Any positive-sum integer normal whose face contains the derivative
generator and another strictly negative-grade exponent points rightward and
at most horizontally. The second exponent lies at least two grades below the
diagonal. -/
theorem oneSided_two_point_normal_sign (ρ σ : ℤ) (p : ℕ × ℕ)
    (hsum : 0 < ρ + σ) (hgrade : p.1 < p.2) (hne : p ≠ (0, 1))
    (hweight : ρ * (p.1 : ℤ) + σ * (p.2 : ℤ) = σ) :
    0 < ρ ∧ σ ≤ 0 ∧ p.1 + 1 < p.2 := by
  have hj : 1 < p.2 := by
    by_contra hn
    have hle : p.2 ≤ 1 := by omega
    have hi : p.1 = 0 := by omega
    have hj' : p.2 = 1 := by omega
    exact hne (Prod.ext hi hj')
  have hgap : (p.1 : ℤ) ≤ (p.2 : ℤ) - 1 := by
    have h : p.1 + 1 ≤ p.2 := by omega
    omega
  have hgapStrict : p.1 + 1 < p.2 := by
    by_contra hn
    have heq : p.2 = p.1 + 1 := by omega
    have hEqZ : (p.2 : ℤ) = (p.1 : ℤ) + 1 := by exact_mod_cast heq
    rw [hEqZ] at hweight
    have hi : p.1 = 0 := by
      have hprod : (ρ + σ) * (p.1 : ℤ) = 0 := by nlinarith [hweight]
      have hsumne : ρ + σ ≠ 0 := ne_of_gt hsum
      have hz := (mul_eq_zero.mp hprod).resolve_left hsumne
      exact_mod_cast hz
    have hj' : p.2 = 1 := by omega
    exact hne (Prod.ext hi hj')
  have hσ : σ ≤ 0 := by
    by_contra hn
    have hσpos : 0 < σ := by omega
    by_cases hi : p.1 = 0
    · have hjz : 0 < (p.2 : ℤ) - 1 := by
        have hcast : (1 : ℤ) < p.2 := by exact_mod_cast hj
        omega
      simp [hi] at hweight
      nlinarith [mul_pos hσpos hjz]
    · have hiz : 0 < (p.1 : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hi)
      have hgapz : 0 ≤ (p.2 : ℤ) - 1 - p.1 := by omega
      have hfirst : 0 < (ρ + σ) * (p.1 : ℤ) := mul_pos hsum hiz
      have hsecond : 0 ≤ σ * ((p.2 : ℤ) - 1 - p.1) :=
        mul_nonneg hσpos.le hgapz
      nlinarith [hfirst, hsecond, hweight]
  exact ⟨by omega, hσ, hgapStrict⟩

end Dixmier.Weyl
