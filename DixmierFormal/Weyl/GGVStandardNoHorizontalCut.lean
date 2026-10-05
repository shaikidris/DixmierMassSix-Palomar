/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedCrossingSelection
public import DixmierFormal.Weyl.GGVDiagonalStartAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The no-cut branch of G13 standardization

A subrectangular support has a top-right occupied corner. If its
horizontal face is a singleton and that corner has negative diagonal
grade, its horizontal starting grade is negative. The ramified-cut
branch of G13 Corollary 6.11 is not asserted here.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- A polynomial Weyl operator has an occupied top-right PBW corner
and all occupied exponents lie in its southwest rectangle. -/
def IsSubrectangularAt (P : A1 ℂ) (a b : ℕ) : Prop :=
  expo a b ∈ (symbol P.1).support ∧
    ∀ e ∈ (symbol P.1).support, e 0 ≤ a ∧ e 1 ≤ b

/-- A total-degree bound and a lower bound on the project's diagonal
grade control the second PBW exponent. This is the direct arithmetic
half of G13 Lemma 6.7 (whose diagonal weight is the negative of `grade`). -/
theorem support_second_coord_le_of_diagonal_grade_bound
    (P : A1 ℂ) (b a : ℕ)
    (htotal : ∀ e ∈ (symbol P.1).support, e 0 + e 1 ≤ a + b)
    (hgrade : ∀ e ∈ (symbol P.1).support, (a : ℤ) - b ≤ grade e) :
    ∀ e ∈ (symbol P.1).support, e 1 ≤ b := by
  intro e he
  have htotal' : (e 0 : ℤ) + e 1 ≤ (a : ℤ) + b := by
    exact_mod_cast htotal e he
  have hgrade' := hgrade e he
  have hy : (e 1 : ℤ) ≤ b := by
    dsimp [grade] at hgrade'
    omega
  exact_mod_cast hy

/-- The subrectangular corner is the unique occupied total-degree
leading point. -/
theorem subrectangular_diagonal_face_unique
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b) :
    expo a b ∈ (leadingForm 1 1 P.1).support ∧
      ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b := by
  have hc : expo a b ∈ (leadingForm 1 1 P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) (expo a b)).mpr
    refine ⟨hrect.1, ?_⟩
    intro e he
    obtain ⟨hx, hy⟩ := hrect.2 e he
    dsimp [rationalNewtonWeight]
    simp [expo]
    exact_mod_cast (Nat.add_le_add hx hy)
  refine ⟨hc, ?_⟩
  intro e he
  have heS := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) e).mp he
  have hcS := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) (expo a b)).mp hc
  obtain ⟨hx, hy⟩ := hrect.2 e heS.1
  have hle := heS.2 (expo a b) hcS.1
  dsimp [rationalNewtonWeight] at hle
  simp [expo] at hle
  have hxy : e 0 + e 1 = a + b := by
    have hq : (a : ℚ) + b ≤ e 0 + e 1 := by linarith
    exact_mod_cast le_antisymm (Nat.add_le_add hx hy) (by exact_mod_cast hq)
  have hxe : e 0 = a := by omega
  have hye : e 1 = b := by omega
  ext i
  fin_cases i
  · simpa [expo] using hxe
  · simpa [expo] using hye

/-- With the preliminary companion, a positive-degree subrectangular
counterexample cannot have its top-right corner on the grade-zero line. -/
theorem counterexample_subrectangular_corner_not_diagonal
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b)
    (hpos : 0 < a + b) : a ≠ b := by
  intro hab
  have ha : 0 < a := by omega
  obtain ⟨hc, hsingle⟩ := subrectangular_diagonal_face_unique P a b hrect
  have hmax : ∀ x ∈ (leadingForm 1 1 P.1).support,
      Finsupp.weight (wt 1 (-1)) x ≤
        Finsupp.weight (wt 1 (-1)) (expo a b) := by
    intro x hx
    rw [hsingle x hx]
  exact ggv_preliminary_no_diagonal_leading_top hsource P Q hpair
    1 1 (by norm_num [IsDirection]) hc hmax (by simpa [expo] using hab) (by simpa [expo] using ha)

/-- The top-right corner is the point of maximal first coordinate. -/
theorem subrectangular_corner_mem_horizontal
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b) :
    expo a b ∈ (leadingForm 1 0 P.1).support := by
  apply (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) (expo a b)).mpr
  refine ⟨hrect.1, ?_⟩
  intro e he
  have hle := (hrect.2 e he).1
  dsimp [rationalNewtonWeight]
  simp [expo]
  exact_mod_cast hle

/-- A singleton horizontal face has its starting point at the
subrectangular top-right corner. -/
theorem subrectangular_horizontal_start_negative_of_no_dir
    (P : A1 ℂ) (a b : ℕ)
    (hrect : IsSubrectangularAt P a b) (hab : a < b)
    (hno : ¬ InDir 1 0 P.1) :
    ∃ c ∈ (leadingForm 1 0 P.1).support,
      (∀ e ∈ (leadingForm 1 0 P.1).support, c 1 ≤ e 1) ∧
      grade c < 0 := by
  let c := expo a b
  have hc : c ∈ (leadingForm 1 0 P.1).support :=
    subrectangular_corner_mem_horizontal P a b hrect
  have hcard : (leadingForm 1 0 P.1).support.card ≤ 1 := by
    dsimp [InDir] at hno
    omega
  have hsingle : ∀ e ∈ (leadingForm 1 0 P.1).support, e = c := by
    intro e he
    exact (Finset.card_le_one_iff.mp hcard) he hc
  refine ⟨c, hc, ?_, ?_⟩
  · intro e he
    rw [hsingle e he]
  · dsimp [c, grade]
    simp [expo]
    omega

/-- In the no-horizontal-edge branch, the source's companion and
subrectangular orientation select a genuine negative crossing face.
This is still conditional on producing the standard minimal pair. -/
theorem counterexample_subrectangular_no_cut_strict_crossing
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b) (hab : a < b)
    (hno : ¬ InDir 1 0 P.1) :
    ∃ (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
      (ρ s : ℕ) (u v : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes P)[j]'hj = (-(s : ℤ) : ℚ) / ρ ∧
      InDir (ρ : ℤ) (-(s : ℤ)) P.1 ∧
      InDir (ρ : ℤ) (-(s : ℤ)) Q.1 ∧
      u ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      v ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        u 1 ≤ e 1) ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        e 1 ≤ v 1) ∧ 0 < grade u ∧ grade v < 0 := by
  exact counterexample_ordered_strict_crossing_of_horizontal_start
    hsource P Q hpair
      (subrectangular_horizontal_start_negative_of_no_dir P a b hrect hab hno)

end Dixmier.Weyl
