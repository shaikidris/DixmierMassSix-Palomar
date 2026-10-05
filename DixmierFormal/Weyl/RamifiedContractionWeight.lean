/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedPBWZeroOrder
public import DixmierFormal.Weyl.RamifiedCutWeightSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Laurent support bound for every ramified contraction

If `f` has Laurent exponents at most `B`, then the coefficient at
derivative order `j` in `Y^n f` has exponents at most `B-l(n-j)`.
This all-order estimate separates first contractions from later ones
at a positive-sum Newton weight.
-/

namespace Dixmier.Weyl

theorem LaurentUpper_mul_for_contraction (f g : LaurentPolynomial ℂ) (B C : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C) :
    LaurentUpper (f*g) (B+C) := by
  intro v hv
  have hmul := AddMonoidAlgebra.support_coeff_mul_subset f g hv
  obtain ⟨i, hi, u, hu, rfl⟩ := Finset.mem_add.mp hmul
  have hfi := hf i hi
  have hgu := hg u hu
  omega

/-- A common Laurent support bound survives any finite sum. This is the
support adapter for the PBW commutator double sum. -/
theorem LaurentUpper_finset_sum_for_contraction {α : Type*}
    (s : Finset α) (F : α → LaurentPolynomial ℂ) (B : ℤ)
    (hF : ∀ a ∈ s, LaurentUpper (F a) B) :
    LaurentUpper (∑ a ∈ s, F a) B := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact LaurentUpper_zero B
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply LaurentUpper_add
      · exact hF a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hF b (Finset.mem_insert_of_mem hb)

/-- Terms strictly below a selected Laurent exponent contribute zero
there, even after both finite PBW sums have been taken. -/
theorem LaurentUpper_double_sum_coeff_zero {α β : Type*}
    (s : Finset α) (t : Finset β)
    (F : α → β → LaurentPolynomial ℂ) (B v : ℤ)
    (hF : ∀ a ∈ s, ∀ b ∈ t, LaurentUpper (F a b) B)
    (hv : B < v) :
    (∑ a ∈ s, ∑ b ∈ t, F a b).coeff v = 0 := by
  have houter : LaurentUpper (∑ a ∈ s, ∑ b ∈ t, F a b) B := by
    apply LaurentUpper_finset_sum_for_contraction
    intro a ha
    apply LaurentUpper_finset_sum_for_contraction
    exact hF a ha
  by_contra hnz
  have hmem : v ∈ (∑ a ∈ s, ∑ b ∈ t, F a b).coeff.support :=
    Finsupp.mem_support_iff.mpr hnz
  exact (not_le_of_gt hv) (houter v hmem)

/-- An atomwise strict Newton-weight bound excludes a chosen coefficient
from the full finite double sum at a fixed derivative order. -/
theorem ramifiedWeight_double_sum_coeff_zero
    {α β : Type*} (s : Finset α) (t : Finset β)
    (F : α → β → LaurentPolynomial ℂ)
    (l : ℕ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (r : ℕ) (W v : ℤ)
    (hF : ∀ a ∈ s, ∀ b ∈ t, ∀ u ∈ (F a b).coeff.support,
      ramifiedWeight l ρ σ (u,r) < W)
    (hv : W ≤ ramifiedWeight l ρ σ (v,r)) :
    (∑ a ∈ s, ∑ b ∈ t, F a b).coeff v = 0 := by
  apply LaurentUpper_double_sum_coeff_zero s t F (v-1) v
  · intro a ha b hb u hu
    have hstrict := hF a ha b hb u hu
    unfold ramifiedWeight at hstrict hv
    have huv : u < v := by nlinarith
    omega
  · omega

theorem ramifiedDerivativePBWPower_upper (l : ℕ)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) (n j : ℕ) :
    LaurentUpper (ramifiedDerivativePBWPower l f n j)
      (B - (l : ℤ) * ((n : ℤ) - (j : ℤ))) := by
  induction n generalizing j with
  | zero =>
      by_cases hj : j = 0
      · subst j
        simpa [ramifiedDerivativePBWPower] using hf
      · have hz : ramifiedDerivativePBWPower l f 0 j = 0 := by
          simp [ramifiedDerivativePBWPower, hj]
        rw [hz]
        exact LaurentUpper_zero _
  | succ n ih =>
      rw [ramifiedDerivativePBWPower, ramifiedDerivativeLeftLinear_apply]
      have hprev : LaurentUpper
          (if j = 0 then 0 else ramifiedDerivativePBWPower l f n (j-1))
          (B - (l : ℤ) * (((n+1 : ℕ) : ℤ) - (j : ℤ))) := by
        by_cases hj : j = 0
        · simp [hj, LaurentUpper_zero]
        · simp only [hj, ↓reduceIte]
          have heq :
              B - (l : ℤ) * ((n : ℤ) - ((j-1 : ℕ) : ℤ)) =
                B - (l : ℤ) * (((n+1 : ℕ) : ℤ) - (j : ℤ)) := by
            have hjcast : ((j-1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
            rw [hjcast]
            push_cast
            ring
          rw [← heq]
          exact ih (j-1)
      have hderiv : LaurentUpper
          (ramifiedDerivative l (ramifiedDerivativePBWPower l f n j))
          (B - (l : ℤ) * (((n+1 : ℕ) : ℤ) - (j : ℤ))) := by
        have h := LaurentUpper_derivative l _ _ (ih j)
        convert h using 1
        push_cast
        ring
      exact LaurentUpper_add _ _ _ hprev hderiv

theorem LaurentUpper_T (u : ℤ) :
    LaurentUpper (LaurentPolynomial.T u : LaurentPolynomial ℂ) u := by
  intro v hv
  have hnz : (LaurentPolynomial.T u : LaurentPolynomial ℂ).coeff v ≠ 0 :=
    Finsupp.mem_support_iff.mp hv
  simp only [LaurentPolynomial.T_apply] at hnz
  by_cases huv : u = v
  · omega
  · simp [huv] at hnz

theorem ramifiedDerivativePBWPower_monomial_exponent_upper
    (l : ℕ) (u v : ℤ) (n j : ℕ)
    (hv : v ∈ (ramifiedDerivativePBWPower l
      (LaurentPolynomial.T u) n j).coeff.support) :
    v ≤ u - (l : ℤ) * ((n : ℤ) - (j : ℤ)) :=
  ramifiedDerivativePBWPower_upper l _ u (LaurentUpper_T u) n j v hv

theorem ramifiedPBWCoeffs_atomProduct_upper (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (B C : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m r : ℕ) :
    LaurentUpper
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) (r+m))
      (B+C-(l : ℤ) * ((n : ℤ)-(r : ℤ))) := by
  rw [ramifiedPBWCoeffs_atomProduct_all]
  have h := LaurentUpper_mul_for_contraction f (ramifiedDerivativePBWPower l g n r)
    B (C-(l : ℤ) * ((n : ℤ)-(r : ℤ))) hf
    (ramifiedDerivativePBWPower_upper l g C hg n r)
  convert h using 1 <;> ring

/-- A coefficient produced by `n-r` contractions lies at least that
many positive weight steps below the sum of the input atom weights. -/
theorem ramifiedPBWCoeffs_atomProduct_weight_upper
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (f g : LaurentPolynomial ℂ) (B C : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m r : ℕ) (v : ℤ)
    (hv : v ∈
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) (r+m)).coeff.support) :
    ramifiedWeight l ρ σ (v,r+m) ≤
      ρ * (B+C) + (l : ℤ) * σ * ((n : ℤ)+(m : ℤ)) -
        (l : ℤ) * (ρ+σ) * ((n : ℤ)-(r : ℤ)) := by
  have hvbound := ramifiedPBWCoeffs_atomProduct_upper
    l hl f g B C hf hg n m r v hv
  have hscaled := mul_le_mul_of_nonneg_left hvbound (le_of_lt hρ)
  unfold ramifiedWeight
  simp only [Nat.cast_add]
  nlinarith [hscaled]

theorem ramifiedPBWCoeffs_atomProduct_below_first_of_defect
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (f g : LaurentPolynomial ℂ) (B C A D : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m r : ℕ) (hc : r + 1 ≤ n)
    (hP : ρ * B + (l : ℤ) * σ * (n : ℤ) ≤ A)
    (hQ : ρ * C + (l : ℤ) * σ * (m : ℤ) ≤ D)
    (hdefect : ρ * B + (l : ℤ) * σ * (n : ℤ) < A ∨
      ρ * C + (l : ℤ) * σ * (m : ℤ) < D ∨ r + 2 ≤ n)
    (v : ℤ)
    (hv : v ∈
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) (r+m)).coeff.support) :
    ramifiedWeight l ρ σ (v,r+m) < A+D-(l : ℤ)*(ρ+σ) := by
  have hw := ramifiedPBWCoeffs_atomProduct_weight_upper
    l hl ρ σ hρ f g B C hf hg n m r v hv
  have hlz : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  have hstep : (0 : ℤ) < (l : ℤ) * (ρ+σ) := mul_pos hlz hsum
  have hgap : (1 : ℤ) ≤ (n : ℤ) - (r : ℤ) := by omega
  rcases hdefect with hPstrict | hQstrict | hmore
  · nlinarith
  · nlinarith
  · have hgap2 : (2 : ℤ) ≤ (n : ℤ) - (r : ℤ) := by omega
    nlinarith

/-- Two or more contractions of a ramified monomial pair lie below
the first-contraction weight whenever `ρ>0` and `ρ+σ>0`. -/
theorem ramified_monomial_higher_contraction_below_first
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (i u v : ℤ) (n j k : ℕ) (htwo : j + 2 ≤ n)
    (hv : v ∈ (ramifiedDerivativePBWPower l
      (LaurentPolynomial.T u) n j).coeff.support) :
    ramifiedWeight l ρ σ (i+v, j+k) <
      ramifiedWeight l ρ σ (i+u, n+k) -
        (l : ℤ) * (ρ + σ) := by
  have hvbound := ramifiedDerivativePBWPower_monomial_exponent_upper
    l u v n j hv
  have hlz : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  have hgap : (2 : ℤ) ≤ (n : ℤ) - (j : ℤ) := by omega
  have hweight : (0 : ℤ) < (l : ℤ) * (ρ + σ) := mul_pos hlz hsum
  have hmul :
      (l : ℤ) * (ρ + σ) <
        (l : ℤ) * (ρ + σ) * ((n : ℤ) - (j : ℤ)) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hvbound (le_of_lt hρ)
  unfold ramifiedWeight
  simp only [Nat.cast_add]
  nlinarith [hscaled, hmul]

end Dixmier.Weyl
