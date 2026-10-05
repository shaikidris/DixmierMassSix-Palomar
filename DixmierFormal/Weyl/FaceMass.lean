/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Validation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Face term count and operator mass

For a direction of positive weight sum, distinct monomials on one
weighted-homogeneous face have distinct PBW grades. Hence the number
of face monomials is at most the mass of the whole operator.
-/

namespace Dixmier.Weyl

open MvPolynomial
set_option maxHeartbeats 1000000

/-- The support of a weighted component is contained in the original
polynomial support. -/
theorem weightedComponent_support_subset
    (F : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ) :
    (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m F).support ⊆ F.support := by
  intro d hd
  have hcoeff : MvPolynomial.coeff d
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ) m F) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
  split_ifs at hcoeff with hw
  · exact MvPolynomial.mem_support_iff.mpr hcoeff
  · exact False.elim (hcoeff rfl)

/-- Every face grade is an actual grade of the full PBW symbol. -/
theorem face_grade_support_subset (T : A1 ℂ) (ρ σ : ℤ) :
    (leadingForm ρ σ T.1).support.image grade ⊆
      (symbol T.1).support.image grade := by
  apply Finset.image_subset_image
  exact weightedComponent_support_subset (symbol T.1) ρ σ (vDeg ρ σ T.1)

/-- Distinct monomials of a weighted-homogeneous face have different
grades when `ρ+σ>0`. -/
theorem grade_injective_on_homogeneous_face
    (F : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hsum : 0 < ρ + σ)
    (hhom : F.IsWeightedHomogeneous (wt ρ σ) m) :
    Set.InjOn grade F.support := by
  intro d hd e he hgrade
  have hdweight := hhom (MvPolynomial.mem_support_iff.mp hd)
  have heweight := hhom (MvPolynomial.mem_support_iff.mp he)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  obtain ⟨⟨k, l⟩, rfl⟩ := expo_surjective e
  rw [expo_weight] at hdweight heweight
  change (i : ℤ) * ρ + (j : ℤ) * σ = m at hdweight
  change (k : ℤ) * ρ + (l : ℤ) * σ = m at heweight
  have hgrade' : (i : ℤ) - j = (k : ℤ) - l := by
    simpa [grade, expo] using hgrade
  have hdiff : (i : ℤ) - k = (j : ℤ) - l := by omega
  have hweightdiff : ρ * ((i : ℤ) - k) + σ * ((j : ℤ) - l) = 0 := by
    nlinarith [hdweight, heweight]
  have hprod : (ρ + σ) * ((j : ℤ) - l) = 0 := by
    calc
      (ρ + σ) * ((j : ℤ) - l) =
          ρ * ((i : ℤ) - k) + σ * ((j : ℤ) - l) := by rw [hdiff]; ring
      _ = 0 := hweightdiff
  have hj : j = l := by
    have hz := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hsum)
    omega
  have hi : i = k := by omega
  simp [hi, hj]

/-- The paper's face-to-mass estimate, with no degree or mate bound. -/
theorem face_term_count_le_mass (T : A1 ℂ) (ρ σ : ℤ)
    (hsum : 0 < ρ + σ) :
    (leadingForm ρ σ T.1).support.card ≤ mass T.1 := by
  have hhom : (leadingForm ρ σ T.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ T.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T.1) (w := wt ρ σ) (n := vDeg ρ σ T.1)
  have hinj := grade_injective_on_homogeneous_face
    (leadingForm ρ σ T.1) ρ σ (vDeg ρ σ T.1) hsum hhom
  calc
    (leadingForm ρ σ T.1).support.card =
        ((leadingForm ρ σ T.1).support.image grade).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((symbol T.1).support.image grade).card :=
      Finset.card_le_card (face_grade_support_subset T ρ σ)
    _ = mass T.1 := rfl

end Dixmier.Weyl
