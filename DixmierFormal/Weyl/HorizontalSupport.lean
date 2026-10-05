/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalGGVScalar
public import DixmierFormal.Weyl.CrossingGrade
public import DixmierFormal.Weyl.CrossingTermCount
public import DixmierFormal.Scalar.HorizontalSquare

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Coefficients of a horizontal homogeneous base

The coefficient at `(a,j)` of `x^a g(y)` is exactly the coefficient of `y^j`
in `g`. This is the support-level bridge needed to recover the order and
degree inequalities from a genuine strict-crossing face.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem horizontal_base_coeff (g : ℂ[X]) (a j : ℕ) :
    MvPolynomial.coeff (expo a j)
      (MvPolynomial.X 0 ^ a * g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) =
      g.coeff j := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval₂_add, mul_add, MvPolynomial.coeff_add,
        Polynomial.coeff_add, hp, hq]
  | monomial n c =>
      have hmon : MvPolynomial.X 0 ^ a *
          (Polynomial.monomial n c).eval₂ MvPolynomial.C (MvPolynomial.X 1) =
          MvPolynomial.monomial (expo a n) c := by
        simp [Polynomial.eval₂_monomial, expo, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
      rw [hmon]
      simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, expo]
      simp only [add_left_cancel_iff]
      by_cases h : n = j
      · subst j
        simp
      · have hs : Finsupp.single (1 : Fin 2) n ≠ Finsupp.single 1 j :=
          fun heq => h ((Finsupp.single_injective (1 : Fin 2)).eq_iff.mp heq)
        simp [h, hs]

theorem horizontal_base_coeff_general (g : ℂ[X]) (a i j : ℕ) :
    MvPolynomial.coeff (expo i j)
      (MvPolynomial.X 0 ^ a * g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) =
      if i = a then g.coeff j else 0 := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval₂_add, mul_add, MvPolynomial.coeff_add,
        Polynomial.coeff_add, hp, hq]
      split_ifs <;> simp
  | monomial n c =>
      have hmon : MvPolynomial.X 0 ^ a *
          (Polynomial.monomial n c).eval₂ MvPolynomial.C (MvPolynomial.X 1) =
          MvPolynomial.monomial (expo a n) c := by
        simp [Polynomial.eval₂_monomial, expo, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
      rw [hmon]
      simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      by_cases hi : i = a
      · subst i
        simp only [↓reduceIte]
        by_cases hj : n = j
        · subst j
          simp
        · have hne : expo a n ≠ expo a j :=
            fun heq => by
              have hp : (a, n) = (a, j) := expo_injective heq
              exact hj (congrArg Prod.snd hp)
          simp [hj, hne]
      · have hne : expo a n ≠ expo i j :=
          fun heq => by
            have hp : (a, n) = (i, j) := expo_injective heq
            exact hi (congrArg Prod.fst hp).symm
        simp [hi, hne]

theorem horizontal_base_support_iff (g : ℂ[X]) (a i j : ℕ) :
    expo i j ∈
      ((MvPolynomial.X (0 : Fin 2) ^ a *
        g.eval₂ MvPolynomial.C (MvPolynomial.X (1 : Fin 2))) :
        MvPolynomial (Fin 2) ℂ).support ↔
      i = a ∧ j ∈ g.support := by
  rw [MvPolynomial.mem_support_iff, horizontal_base_coeff_general]
  by_cases hi : i = a <;> simp [hi, Polynomial.mem_support_iff]

theorem horizontal_base_nonpos_of_support_ge
    (g : ℂ[X]) (a : ℕ)
    (h : ∀ j ∈ g.support, a ≤ j) :
    ∀ d ∈ (MvPolynomial.X (0 : Fin 2) ^ a *
      g.eval₂ MvPolynomial.C (MvPolynomial.X (1 : Fin 2))).support,
      grade d ≤ 0 := by
  intro d hd
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  obtain ⟨hia, hj⟩ := (horizontal_base_support_iff g a i j).mp hd
  have hja := h j hj
  subst i
  simp [grade, expo]
  omega

theorem support_grade_nonneg_mul
    (R S : MvPolynomial (Fin 2) ℂ)
    (hR : ∀ d ∈ R.support, 0 ≤ grade d)
    (hS : ∀ d ∈ S.support, 0 ≤ grade d) :
    ∀ d ∈ (R * S).support, 0 ≤ grade d := by
  intro d hd
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul R S hd)
  rw [grade_add]
  exact add_nonneg (hR u hu) (hS v hv)

theorem support_grade_nonneg_pow
    (R : MvPolynomial (Fin 2) ℂ) (k : ℕ)
    (hR : ∀ d ∈ R.support, 0 ≤ grade d) :
    ∀ d ∈ (R ^ k).support, 0 ≤ grade d := by
  induction k with
  | zero =>
      intro d hd
      simp at hd
      simp [hd, grade]
  | succ k ih =>
      rw [pow_succ]
      exact support_grade_nonneg_mul (R ^ k) R ih hR

theorem horizontal_base_nonneg_of_support_le
    (g : ℂ[X]) (a : ℕ)
    (h : ∀ j ∈ g.support, j ≤ a) :
    ∀ d ∈ (MvPolynomial.X (0 : Fin 2) ^ a *
      g.eval₂ MvPolynomial.C (MvPolynomial.X (1 : Fin 2))).support,
      0 ≤ grade d := by
  intro d hd
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  obtain ⟨hia, hj⟩ := (horizontal_base_support_iff g a i j).mp hd
  have hja := h j hj
  subst i
  simp [grade, expo]
  omega

/-- A strict horizontal crossing forces actual support on both sides of `a`. -/
theorem horizontal_crossing_support_straddles
    (P : A1 ℂ) (μ : ℂ) (k a : ℕ) (g : ℂ[X])
    (hμ : μ ≠ 0)
    (hface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a *
        g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ k)
    (hcross : IsStrictCrossing 1 0 P.1) :
    (∃ j ∈ g.support, j < a) ∧ (∃ j ∈ g.support, a < j) := by
  constructor
  · by_contra hnot
    have hge : ∀ j ∈ g.support, a ≤ j := by
      intro j hj
      by_contra h
      exact hnot ⟨j, hj, by omega⟩
    have hR := horizontal_base_nonpos_of_support_ge g a hge
    obtain ⟨d, hd, hpos⟩ := hcross.2.1
    rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ] at hd
    exact not_le_of_gt hpos (support_grade_nonpos_pow _ k hR d hd)
  · by_contra hnot
    have hle : ∀ j ∈ g.support, j ≤ a := by
      intro j hj
      by_contra h
      exact hnot ⟨j, hj, by omega⟩
    have hR := horizontal_base_nonneg_of_support_le g a hle
    obtain ⟨d, hd, hneg⟩ := hcross.2.2
    rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ] at hd
    exact not_le_of_gt hneg (support_grade_nonneg_pow _ k hR d hd)

/-- The support witness below `a` controls the root order at zero; the witness
above `a` controls the polynomial degree. -/
theorem horizontal_crossing_order_bounds
    (P : A1 ℂ) (μ : ℂ) (k a : ℕ) (g : ℂ[X])
    (hμ : μ ≠ 0)
    (hface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a *
        g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ k)
    (hcross : IsStrictCrossing 1 0 P.1) :
    g.rootMultiplicity 0 < a ∧ a < g.natDegree := by
  obtain ⟨⟨j, hj, hja⟩, ⟨t, ht, hat⟩⟩ :=
    horizontal_crossing_support_straddles P μ k a g hμ hface hcross
  constructor
  · rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
    exact lt_of_le_of_lt
      (Polynomial.natTrailingDegree_le_of_ne_zero (Polynomial.mem_support_iff.mp hj)) hja
  · exact lt_of_lt_of_le hat (Polynomial.le_natDegree_of_mem_supp t ht)

theorem horizontal_face_termCount_le_mass
    (P : A1 ℂ) (μ : ℂ) (k a : ℕ) (g : ℂ[X])
    (hμ : μ ≠ 0)
    (hface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a *
        g.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ k) :
    termCount (g ^ k) ≤ mass P.1 := by
  apply crossingFace_general_termCount_le_mass μ a 0 0 1 k g P hμ (by omega)
  simpa using hface

/-- For an actual mass-six counterexample with a strict horizontal crossing,
the source-supplied companion and proved scalar classification force the
quadratic-square face. This is conditional only on the explicit GGV inputs. -/
theorem horizontal_counterexample_mass_six_scalar_shape
    (H : GGVInputs) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q)
    (hcross : IsStrictCrossing 1 0 P.1)
    (hmass : mass P.1 ≤ 6) :
    ∃ (μ c β : ℂ), μ ≠ 0 ∧ c ≠ 0 ∧ β ≠ 0 ∧
      leadingForm 1 0 P.1 = MvPolynomial.C μ *
        (MvPolynomial.X 0 *
          (Polynomial.C c * (Polynomial.X - Polynomial.C β) ^ 2).eval₂
            MvPolynomial.C (MvPolynomial.X 1)) ^ 2 := by
  obtain ⟨μ, k, a, g, f, hμ, hk, hg, hface, hcomp⟩ :=
    horizontal_counterexample_scalar_of_GGV H P Q hpair
  have hb := horizontal_crossing_order_bounds P μ k a g hμ hface hcross
  have ht : termCount (g ^ k) ≤ 6 :=
    (horizontal_face_termCount_le_mass P μ k a g hμ hface).trans hmass
  have hgdeg : 0 < g.natDegree := by omega
  obtain ⟨hk2, ha1, _⟩ := hcomp.mass_six_parameters hgdeg hb.2 hb.1 hk ht
  subst k
  subst a
  obtain ⟨c, β, hc, hβ, hshape⟩ := hcomp.mass_six_quadratic hgdeg hb.1 ht
  refine ⟨μ, c, β, hμ, hc, hβ, ?_⟩
  simpa [hshape] using hface

end Dixmier.Weyl
