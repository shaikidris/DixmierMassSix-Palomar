/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVRationalFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Primitive direction of a rational Newton face

A rational slope strictly between the diagonal and horizontal slopes
has a primitive positive-sum integer normal given by its reduced
denominator and numerator.
-/

namespace Dixmier.Weyl

/-- A rational slope in `(-1,0)` gives a primitive strict-negative
direction in the paper's convention. -/
theorem rationalSlope_primitive_negative_direction
    (t : ℚ) (hleft : -1 < t) (hright : t < 0) :
    IsDirection (t.den : ℤ) t.num ∧
      0 < (t.den : ℤ) ∧ t.num < 0 ∧
      (t.num : ℚ) / (t.den : ℚ) = t := by
  have hdenQ : (0 : ℚ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hdenZ : (0 : ℤ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hnum : t * (t.den : ℚ) = (t.num : ℚ) := by
    calc
      t * (t.den : ℚ) =
          ((t.num : ℚ) / (t.den : ℚ)) * (t.den : ℚ) := by
            rw [Rat.num_div_den]
      _ = (t.num : ℚ) := by field_simp
  have hnumNegQ : (t.num : ℚ) < 0 := by
    rw [← hnum]
    exact mul_neg_of_neg_of_pos hright hdenQ
  have hnumNeg : t.num < 0 := by exact_mod_cast hnumNegQ
  have hsumQ : (0 : ℚ) < (t.den : ℚ) + t.num := by
    have hmul := mul_lt_mul_of_pos_right hleft hdenQ
    rw [hnum] at hmul
    linarith
  have hsum : (0 : ℤ) < (t.den : ℤ) + t.num := by
    exact_mod_cast hsumQ
  have hcop : Int.gcd (t.den : ℤ) t.num = 1 := by
    simpa [Int.gcd_def, Nat.gcd_comm, Nat.Coprime] using t.reduced.symm
  exact ⟨⟨hcop,hsum⟩, hdenZ, hnumNeg, Rat.num_div_den t⟩

/-- A rational slope strictly above the diagonal has a primitive positive
integer normal whose second coordinate is strictly larger than its first.
This is the rational-to-integral bridge used by the positive-successor
argument in G13 Lemma 6.7. -/
theorem rationalSlope_primitive_positive_direction
    (t : ℚ) (hone : 1 < t) :
    IsDirection (t.den : ℤ) t.num ∧
      0 < (t.den : ℤ) ∧ (t.den : ℤ) < t.num ∧
      (t.num : ℚ) / (t.den : ℚ) = t := by
  have hdenQ : (0 : ℚ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hdenZ : (0 : ℤ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hnum : t * (t.den : ℚ) = (t.num : ℚ) := by
    calc
      t * (t.den : ℚ) =
          ((t.num : ℚ) / (t.den : ℚ)) * (t.den : ℚ) := by
            rw [Rat.num_div_den]
      _ = (t.num : ℚ) := by field_simp
  have hltQ : (t.den : ℚ) < t.num := by
    have hmul := mul_lt_mul_of_pos_right hone hdenQ
    rw [hnum] at hmul
    simpa using hmul
  have hlt : (t.den : ℤ) < t.num := by
    exact_mod_cast hltQ
  have hsum : (0 : ℤ) < (t.den : ℤ) + t.num := by
    omega
  have hcop : Int.gcd (t.den : ℤ) t.num = 1 := by
    simpa [Int.gcd_def, Nat.gcd_comm, Nat.Coprime] using t.reduced.symm
  exact ⟨⟨hcop, hsum⟩, hdenZ, hlt, Rat.num_div_den t⟩

/-- The reduced numerator and denominator of a rational slope are coprime
as natural numbers.  This form is used when a rational face normal is fed to
the positive-companion lemmas, whose lattice parameters are natural. -/
theorem rationalSlope_numDen_natCoprime (t : ℚ) :
    Nat.Coprime t.den t.num.natAbs := by
  exact t.reduced.symm

/-- Rational maximizers are actual support points of the integer
leading face with the reduced denominator-numerator normal. -/
theorem rationalSlope_maximizer_mem_leadingForm
    (P : A1 ℂ) (t : ℚ) (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (symbol P.1).support)
    (hmax : ∀ b ∈ (symbol P.1).support,
      rationalNewtonWeight t b ≤ rationalNewtonWeight t a) :
    a ∈ (leadingForm (t.den : ℤ) t.num P.1).support := by
  have hρ : (0 : ℤ) < t.den := by
    exact_mod_cast Rat.den_pos t
  apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ) t.num hρ a).mpr
  have hnorm : (t.num : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    simpa using Rat.num_div_den t
  rw [hnorm]
  exact ⟨ha,hmax⟩

/-- Two distinct maximizers at a rational slope in `(-1,0)` give a
genuine primitive negative face direction, hence an entry of the
actual ordered slope list. -/
theorem rationalSlope_two_maximizers_mem_ordered_negative_slopes
    (P : A1 ℂ) (t : ℚ) (hleft : -1 < t) (hright : t < 0)
    (a b : Fin 2 →₀ ℕ)
    (ha : a ∈ (symbol P.1).support)
    (hb : b ∈ (symbol P.1).support)
    (hmax : ∀ p ∈ (symbol P.1).support,
      rationalNewtonWeight t p ≤ rationalNewtonWeight t a)
    (htie : rationalNewtonWeight t b = rationalNewtonWeight t a)
    (hne : a ≠ b) :
    IsDirection (t.den : ℤ) t.num ∧
      InDir (t.den : ℤ) t.num P.1 ∧
      t ∈ ggvOrderedNegativeFaceSlopes P := by
  obtain ⟨hdir,hρ,hσ,hslope⟩ :=
    rationalSlope_primitive_negative_direction t hleft hright
  have haFace := rationalSlope_maximizer_mem_leadingForm P t a ha hmax
  have hbMax : ∀ p ∈ (symbol P.1).support,
      rationalNewtonWeight t p ≤ rationalNewtonWeight t b := by
    intro p hp
    exact (hmax p hp).trans_eq htie.symm
  have hbFace := rationalSlope_maximizer_mem_leadingForm P t b hb hbMax
  have hface : InDir (t.den : ℤ) t.num P.1 := by
    exact Finset.one_lt_card_iff.mpr ⟨a,b,haFace,hbFace,hne⟩
  refine ⟨hdir,hface,?_⟩
  apply (mem_ggvOrderedNegativeFaceSlopes_iff P t).mpr
  refine ⟨((t.den : ℤ),t.num), ?_, ?_⟩
  · exact ⟨hdir,hρ,hσ,hface⟩
  · exact hslope.symm

end Dixmier.Weyl
