/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalStartAdapter
public import DixmierFormal.Weyl.GGVPairedFaceSuccessor
public import DixmierFormal.Weyl.GGVOrderedFaceCanonical

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Zero grade at the first endpoint of a negative face

The minimum derivative-order point on a strict-negative face is its
maximum diagonal-grade point. This connects the ordered-face chain to
the G13 preliminary companion's diagonal obstruction.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- On a positive-sum strict-negative face, the point of minimum
derivative order has maximum diagonal grade. -/
theorem negative_face_min_y_max_grade
    (P : A1 ℂ) (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (hsum : s < ρ) (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support)
    (hmin : ∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
      a 1 ≤ e 1) :
    ∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
      grade e ≤ grade a := by
  intro e he
  have haw : (ρ : ℤ) * a 0 - (s : ℤ) * a 1 =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    change a ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt (ρ : ℤ) (-(s : ℤ)))
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1) (symbol P.1)).support at ha
    rw [MvPolynomial.support_weightedHomogeneousComponent] at ha
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm,
      sub_eq_add_neg] using (Finset.mem_filter.mp ha).2
  have hew : (ρ : ℤ) * e 0 - (s : ℤ) * e 1 =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    change e ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt (ρ : ℤ) (-(s : ℤ)))
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1) (symbol P.1)).support at he
    rw [MvPolynomial.support_weightedHomogeneousComponent] at he
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm,
      sub_eq_add_neg] using (Finset.mem_filter.mp he).2
  have hρz : (0 : ℤ) < ρ := by exact_mod_cast hρ
  have hsumz : (s : ℤ) < ρ := by exact_mod_cast hsum
  have hy : (a 1 : ℤ) ≤ e 1 := by exact_mod_cast hmin e he
  have hprod : 0 ≤ ((ρ : ℤ) - s) * ((e 1 : ℤ) - a 1) :=
    mul_nonneg (by omega) (by omega)
  dsimp [grade]
  nlinarith [hprod]

/-- Conditional on the published preliminary companion, the first
endpoint of any actual strict-negative face cannot have grade zero. -/
theorem ggv_preliminary_negative_face_min_y_grade_ne_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support)
    (hmin : ∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
      a 1 ≤ e 1) : grade a ≠ 0 := by
  intro hzero
  have hsum : s < ρ := by
    have h : (0 : ℤ) < (ρ : ℤ) - s := by simpa using hdir.2
    omega
  have hdiag : a 0 = a 1 := by
    dsimp [grade] at hzero
    omega
  have hPpos := counterexample_vDeg_pos_all_directions
    P Q hpair (ρ : ℤ) (-(s : ℤ)) hdir
  have haw : (ρ : ℤ) * a 0 - (s : ℤ) * a 1 =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    change a ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt (ρ : ℤ) (-(s : ℤ)))
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1) (symbol P.1)).support at ha
    rw [MvPolynomial.support_weightedHomogeneousComponent] at ha
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm,
      sub_eq_add_neg] using (Finset.mem_filter.mp ha).2
  have hapos : 0 < a 0 := by
    rw [← hdiag] at haw
    by_contra hbad
    have hazero : a 0 = 0 := by omega
    rw [hazero] at haw
    simp at haw
    omega
  have hmax := negative_face_min_y_max_grade P ρ s hρ hs hsum a ha hmin
  have hmaxWeight : ∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
      Finsupp.weight (wt 1 (-1)) e ≤
        Finsupp.weight (wt 1 (-1)) a := by
    intro e he
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, grade,
      mul_comm, sub_eq_add_neg] using hmax e he
  exact ggv_preliminary_no_diagonal_leading_top hsource P Q hpair
    ρ (-(s : ℤ)) hdir ha hmaxWeight hdiag hapos

/-- Under the preliminary companion input, every entry of the actual
ordered strict-negative face list has a first endpoint of nonzero grade. -/
theorem ggv_preliminary_ordered_negative_start_grade_ne_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length) :
    ∃ (ρ s : ℕ) (a : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧
      IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes P)[j] = (-(s : ℤ) : ℚ) / ρ ∧
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        a 1 ≤ e 1) ∧ grade a ≠ 0 := by
  have hmem : (ggvOrderedNegativeFaceSlopes P)[j] ∈
      ggvOrderedNegativeFaceSlopes P := List.getElem_mem hj
  obtain ⟨ρ, s, hρ, hs, hdir, hface, hentry, _, _⟩ :=
    ggv_ordered_negative_entry_nat_face P _ hmem
  obtain ⟨p, q, hp, _, _⟩ := Finset.one_lt_card_iff.mp hface
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image
    (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support
      (fun e => e 1) ⟨p, hp⟩
  exact ⟨ρ, s, a, hρ, hs, hdir, hentry, ha, hmin,
    ggv_preliminary_negative_face_min_y_grade_ne_zero
      hsource P Q hpair ρ s hρ hs hdir a ha hmin⟩

end Dixmier.Weyl
