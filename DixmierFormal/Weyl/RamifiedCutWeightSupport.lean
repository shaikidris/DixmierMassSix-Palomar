/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutCoeffRecurrence
public import Mathlib.Algebra.MonoidAlgebra.Support

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Laurent-support transport in the ramified cut

The derivative sends the coefficient at exponent `i+l` to exponent `i`.
This is the support-level ingredient needed to lift the all-degree PBW
recurrence to a Newton-weight filtration.
-/
namespace Dixmier.Weyl

theorem ramifiedDerivative_coeff (l : ℕ)
    (f : LaurentPolynomial ℂ) (i : ℤ) :
    (ramifiedDerivative l f).coeff i =
      (((i + (l : ℤ) : ℤ) : ℂ) / (l : ℂ)) *
        f.coeff (i + (l : ℤ)) := by
  classical
  unfold ramifiedDerivative
  simp only [LinearMap.comp_apply, Finsupp.lsum_apply]
  change (f.coeff.sum fun n c =>
    ((n : ℂ) / (l : ℂ) * c) •
      (LaurentPolynomial.T (n - (l : ℤ)) : LaurentPolynomial ℂ)).coeff i = _
  change (∑ n ∈ f.coeff.support,
    (((n : ℂ) / (l : ℂ) * f.coeff n) •
      (LaurentPolynomial.T (n - (l : ℤ)) : LaurentPolynomial ℂ))).coeff i = _
  rw [AddMonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul_apply]
  rw [Finset.sum_eq_single (i + (l : ℤ))]
  · simp [LaurentPolynomial.T_apply]
  · intro n hn hne
    have hni : n - (l : ℤ) ≠ i := by omega
    simp [LaurentPolynomial.T_apply, hni]
  · intro hnot
    have hz : f.coeff (i + (l : ℤ)) = 0 :=
      Finsupp.notMem_support_iff.mp hnot
    simp [hz]

/-- Every derivative exponent comes from an input exponent shifted by `-l`. -/
theorem ramifiedDerivative_support_subset (l : ℕ)
    (f : LaurentPolynomial ℂ) :
    (ramifiedDerivative l f).coeff.support ⊆
      f.coeff.support.image (fun n => n - (l : ℤ)) := by
  intro i hi
  have hnz : (ramifiedDerivative l f).coeff i ≠ 0 :=
    Finsupp.mem_support_iff.mp hi
  rw [ramifiedDerivative_coeff] at hnz
  have hf : f.coeff (i + (l : ℤ)) ≠ 0 := by
    intro hz
    simp [hz] at hnz
  refine Finset.mem_image.mpr ⟨i + (l : ℤ), ?_, ?_⟩
  · exact Finsupp.mem_support_iff.mpr hf
  · omega

/-- Upper bound on every Laurent exponent, including the zero polynomial. -/
def LaurentUpper (f : LaurentPolynomial ℂ) (B : ℤ) : Prop :=
  ∀ i ∈ f.coeff.support, i ≤ B

theorem LaurentUpper_derivative (l : ℕ)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) :
    LaurentUpper (ramifiedDerivative l f) (B - (l : ℤ)) := by
  intro i hi
  obtain ⟨n,hn,hni⟩ := Finset.mem_image.mp
    ((ramifiedDerivative_support_subset l f) hi)
  have hn := hf n hn
  omega

theorem LaurentUpper_add (f g : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g B) :
    LaurentUpper (f+g) B := by
  intro i hi
  have hsub : (f+g).coeff.support ⊆
      f.coeff.support ∪ g.coeff.support := by
    simpa only [AddMonoidAlgebra.coeff_add] using
      (Finsupp.support_add :
        (f.coeff + g.coeff).support ⊆
          f.coeff.support ∪ g.coeff.support)
  rcases Finset.mem_union.mp (hsub hi) with hfi | hgi
  · exact hf i hfi
  · exact hg i hgi

theorem LaurentUpper_cutShift_mul (l : ℕ) (ρ σ : ℤ)
    (c : ℂ) (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) :
    LaurentUpper (ramifiedCutShift l ρ σ c * f)
      (B + ramifiedCutExponent l ρ σ) := by
  intro i hi
  have hs : (ramifiedCutShift l ρ σ c).coeff.support ⊆
      {ramifiedCutExponent l ρ σ} := by
    rw [ramifiedCutShift, LaurentPolynomial.smul_eq_C_mul]
    exact LaurentPolynomial.support_C_mul_T c _
  have hmul := AddMonoidAlgebra.support_coeff_mul_subset
    (ramifiedCutShift l ρ σ c) f hi
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_add.mp hmul
  have hu' : u = ramifiedCutExponent l ρ σ :=
    Finset.mem_singleton.mp (hs hu)
  have hv' := hf v hv
  omega

theorem LaurentUpper_zero (B : ℤ) :
    LaurentUpper (0 : LaurentPolynomial ℂ) B := by
  intro i hi
  simp at hi

theorem LaurentUpper_mono (f : LaurentPolynomial ℂ)
    (B C : ℤ) (hBC : B ≤ C) (hf : LaurentUpper f B) :
    LaurentUpper f C := by
  intro i hi
  exact (hf i hi).trans hBC

theorem LaurentUpper_one :
    LaurentUpper (1 : LaurentPolynomial ℂ) 0 := by
  intro i hi
  have hnz : (1 : LaurentPolynomial ℂ).coeff i ≠ 0 :=
    Finsupp.mem_support_iff.mp hi
  rw [← LaurentPolynomial.T_zero] at hnz
  simp only [LaurentPolynomial.T_apply] at hnz
  by_cases h0 : (0 : ℤ) = i
  · omega
  · simp [h0] at hnz

/-- The shear exponent is strictly greater than the derivative shift
`-l` in the positive-weight-sum range. -/
theorem ramifiedCutExponent_gt_neg_index (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) :
    -(l : ℤ) < ramifiedCutExponent l ρ σ := by
  have hw := ramifiedCutExponent_weight l ρ σ hdiv
  have hlz : 0 < (l : ℤ) := by exact_mod_cast hl
  nlinarith

/-- Uniform Laurent-exponent upper edge for every derivative coefficient
of every power of the cut-shifted generator. -/
theorem ramifiedCutPower_upper (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n j : ℕ) :
    LaurentUpper
      (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n j)
      (((n : ℤ) - (j : ℤ)) * ramifiedCutExponent l ρ σ) := by
  let k := ramifiedCutExponent l ρ σ
  have hk : -(l : ℤ) < k :=
    ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hpos
  induction n generalizing j with
  | zero =>
      by_cases hj : j = 0
      · subst j
        simpa [ramifiedShiftPBWPower, k] using LaurentUpper_one
      · have hz : (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) 0) j = 0 :=
          ramifiedShiftPBWPower_zero_above l _ 0 j (by omega)
        rw [hz]
        exact LaurentUpper_zero _
  | succ n ih =>
      rw [ramifiedShiftPBWPower, ramifiedShiftPBWStep_apply]
      have hprev : LaurentUpper
          (if j = 0 then 0 else
            (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n) (j-1))
          ((((n+1 : ℕ) : ℤ) - (j : ℤ)) * k) := by
        by_cases hj : j = 0
        · simp [hj, LaurentUpper_zero]
        · simp only [hj, ↓reduceIte]
          have heq : ((n : ℤ) - ((j-1 : ℕ) : ℤ)) * k =
              ((((n+1 : ℕ) : ℤ) - (j : ℤ)) * k) := by
                have hjcast : ((j-1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
                rw [hjcast]
                push_cast
                ring
          rw [← heq]
          exact ih (j-1)
      have hderiv : LaurentUpper
          (ramifiedDerivative l
            ((ramifiedShiftPBWPower l
              (ramifiedCutShift l ρ σ c) n) j))
          ((((n+1 : ℕ) : ℤ) - (j : ℤ)) * k) := by
        apply LaurentUpper_mono _ _ _ _
          (LaurentUpper_derivative l _ _ (ih j))
        change ((n : ℤ) - (j : ℤ)) * k - (l : ℤ) ≤
          (((n+1 : ℕ) : ℤ) - (j : ℤ)) * k
        push_cast
        nlinarith
      have hshift : LaurentUpper
          (ramifiedCutShift l ρ σ c *
            ((ramifiedShiftPBWPower l
              (ramifiedCutShift l ρ σ c) n) j))
          ((((n+1 : ℕ) : ℤ) - (j : ℤ)) * k) := by
        have hh := LaurentUpper_cutShift_mul l ρ σ c _ _ (ih j)
        convert hh using 1
        simp [k]
        ring
      exact LaurentUpper_add _ _ _
        (LaurentUpper_add _ _ _ hprev hderiv) hshift

/-- Every canonical PBW support point of a shifted power lies on or
below the proposed Newton face. -/
theorem ramifiedCutPower_weight_upper (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n : ℕ)
    (i : ℤ) (j : ℕ)
    (hij : (i,j) ∈ ramifiedPBWSupport l hl
      ((ramifiedShiftedYGen l (ramifiedCutShift l ρ σ c))^n)) :
    ramifiedWeight l ρ σ (i,j) ≤
      (n : ℤ) * (l : ℤ) * σ := by
  have hnz := (ramifiedPBWSupport_mem_iff l hl _ i j).mp hij
  simp only [ramifiedPBWCoeff,
    ramifiedShiftPBWPower_canonical] at hnz
  have hupper := ramifiedCutPower_upper l hl ρ σ hρ hdiv hpos c n j
    i (Finsupp.mem_support_iff.mpr hnz)
  have hw := ramifiedCutExponent_weight l ρ σ hdiv
  unfold ramifiedWeight
  nlinarith [mul_le_mul_of_nonneg_left hupper (le_of_lt hρ)]

/-- The top PBW point `Y^n` always survives the shear. -/
theorem ramifiedCutPower_top_support (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) (n : ℕ) :
    ((0 : ℤ),n) ∈ ramifiedPBWSupport l hl
      ((ramifiedShiftedYGen l (ramifiedCutShift l ρ σ c))^n) := by
  apply (ramifiedPBWSupport_mem_iff l hl _ 0 n).mpr
  simp only [ramifiedPBWCoeff,
    ramifiedShiftPBWPower_canonical,
    ramifiedShiftPBWPower_top]
  simp [← LaurentPolynomial.T_zero]

/-- The actual maximum scaled Newton weight of a shifted power is the
weight of `Y^n`; no higher-weight contraction or cancellation occurs. -/
theorem ramifiedCutPower_weightDeg (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n : ℕ) :
    ramifiedWeightDeg l hl ρ σ
      ((ramifiedShiftedYGen l (ramifiedCutShift l ρ σ c))^n) =
      (n : ℤ) * (l : ℤ) * σ := by
  let U := ((ramifiedShiftedYGen l (ramifiedCutShift l ρ σ c))^n)
  let W : ℤ := (n : ℤ) * (l : ℤ) * σ
  have hsup : (ramifiedPBWSupport l hl U).sup
      (fun p => (ramifiedWeight l ρ σ p : WithBot ℤ)) =
      (W : WithBot ℤ) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro p hp
      exact_mod_cast ramifiedCutPower_weight_upper l hl ρ σ
        hρ hdiv hpos c n p.1 p.2 hp
    · have hmem := ramifiedCutPower_top_support l hl ρ σ c n
      have hle : (ramifiedWeight l ρ σ ((0 : ℤ),n) : WithBot ℤ) ≤
          (ramifiedPBWSupport l hl U).sup
            (fun p => (ramifiedWeight l ρ σ p : WithBot ℤ)) :=
        Finset.le_sup (f := fun p =>
          (ramifiedWeight l ρ σ p : WithBot ℤ)) hmem
      have hW : ramifiedWeight l ρ σ ((0 : ℤ),n) = W := by
        dsimp [W, ramifiedWeight]
        ring
      rw [hW] at hle
      exact hle
  simp [ramifiedWeightDeg, U, hsup, W]

end Dixmier.Weyl
