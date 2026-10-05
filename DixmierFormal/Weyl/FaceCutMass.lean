/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FaceMass
public import DixmierFormal.Scalar.Defs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Univariate cut-polynomial support and operator mass

Evaluation of a bivariate face at `x = 1` cannot introduce a new `y` exponent.
Combined with the face-to-mass estimate, this supplies the exact scalar term
bound used in the crossing reductions.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

private theorem eval_monomial_y_exponent (d : Fin 2 →₀ ℕ) :
    (∏ i : Fin 2, (if i = 0 then (1 : ℂ[X]) else Polynomial.X) ^ d i) =
      (Polynomial.X : ℂ[X]) ^ d 1 := by
  simp [Fin.prod_univ_two]

private theorem polynomial_support_sum_subset {α : Type*} (s : Finset α)
    (f : α → ℂ[X]) :
    (∑ d ∈ s, f d).support ⊆ s.biUnion (fun d => (f d).support) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih =>
    simpa [Finset.sum_insert hd, Finset.biUnion_insert] using
      (Polynomial.support_add).trans
        (Finset.union_subset_union (Finset.Subset.refl _) ih)

/-- Evaluation at `x=1` can cancel terms but cannot create a new `y` exponent. -/
theorem cutPolynomial_support_subset_y_exponents (F : MvPolynomial (Fin 2) ℂ) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X) F).support ⊆
    F.support.image (fun d => d 1) := by
  intro n hn
  rw [MvPolynomial.eval₂_eq'] at hn
  simp_rw [eval_monomial_y_exponent] at hn
  have hn' := polynomial_support_sum_subset F.support
    (fun d => Polynomial.C (MvPolynomial.coeff d F) * Polynomial.X ^ d 1) hn
  obtain ⟨d, hd, hne⟩ := Finset.mem_biUnion.mp hn'
  apply Finset.mem_image.mpr
  refine ⟨d, hd, ?_⟩
  exact (Polynomial.mem_support_C_mul_X_pow hne).symm

/-- The cut polynomial has no more terms than its bivariate face. -/
theorem cutPoly_termCount_le_face_support (T : A1 ℂ) (ρ σ : ℤ) :
    termCount (cutPoly ρ σ T.1) ≤ (leadingForm ρ σ T.1).support.card := by
  calc
    termCount (cutPoly ρ σ T.1) = (cutPoly ρ σ T.1).support.card := rfl
    _ ≤ ((leadingForm ρ σ T.1).support.image (fun d => d 1)).card :=
      Finset.card_le_card
        (cutPolynomial_support_subset_y_exponents (leadingForm ρ σ T.1))
    _ ≤ (leadingForm ρ σ T.1).support.card := Finset.card_image_le

/-- The paper's cut-polynomial term count is bounded by whole-operator mass. -/
theorem cutPoly_termCount_le_mass (T : A1 ℂ) (ρ σ : ℤ)
    (hsum : 0 < ρ + σ) :
    termCount (cutPoly ρ σ T.1) ≤ mass T.1 :=
  (cutPoly_termCount_le_face_support T ρ σ).trans (face_term_count_le_mass T ρ σ hsum)

end Dixmier.Weyl
