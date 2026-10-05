/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedPBWReconstruction

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A uniform first-contraction coefficient for ramified PBW atoms

The second atom may have derivative order zero. This packages the
positive-order and order-zero calculations into one formula, including
the extremal Laurent coefficient needed for the finite Newton face.
-/

namespace Dixmier.Weyl

/-- Right multiplication by a derivative power cannot create a PBW
coefficient below that power. -/
theorem ramifiedPBWCoeffs_rightShift_zero_below
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (m j : ℕ) (hj : j < m) :
    ramifiedPBWCoeffs l hl (T * (ramifiedYGen l)^m) j = 0 := by
  rw [ramifiedPBWCoeffs_rightShift]
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨r, hr⟩
  simp only [addRightEmbedding_apply] at hr
  omega

/-- A product of atoms has no coefficient above the sum of their
derivative orders. This is the finite-support bound used to discard
lower-order atom pairs in a full operator commutator. -/
theorem ramifiedPBWCoeffs_atomProduct_zero_above
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m j : ℕ) (hj : n+m < j) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) j = 0 := by
  have hshape :
      (ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) =
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          ramifiedCoeffGen l g) * (ramifiedYGen l)^m := by
    simp only [mul_assoc]
  by_cases hm : j < m
  · rw [hshape]
    exact ramifiedPBWCoeffs_rightShift_zero_below l hl _ m j hm
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hm)
    have hidx : m + r = r + m := by omega
    rw [hidx]
    rw [ramifiedPBWCoeffs_atomProduct_all]
    apply mul_eq_zero_of_right
    exact ramifiedDerivativePBWPower_zero_above l g n r (by omega)

/-- The commutator of two atoms has derivative order strictly less
than the sum of the two input orders. This includes both order-zero
boundaries and the canceled top coefficient. -/
theorem ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m j : ℕ) (hj : n+m ≤ j) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j = 0 := by
  rcases eq_or_lt_of_le hj with heq | hlt
  · subst j
    exact ramifiedPBWCoeffs_atomCommutator_top_zero l hl f g n m
  · rw [ramifiedPBWCoeffs_sub, Finsupp.sub_apply,
      ramifiedPBWCoeffs_atomProduct_zero_above l hl f g n m j hlt,
      ramifiedPBWCoeffs_atomProduct_zero_above l hl g f m n j
        (by omega)]
    simp

/-- For arbitrary finite ramified operators, the commutator has no
coefficient at or above the sum of their PBW derivative orders. No
cutoff on either operator is used. -/
theorem ramifiedPBWCoeffs_commutator_zero_at_or_above_orders
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : ramifiedPBWOrder l hl P + ramifiedPBWOrder l hl Q ≤ j) :
    ramifiedPBWCoeffs l hl (P*Q-Q*P) j = 0 := by
  rw [ramifiedPBWCoeffs_commutator_double_sum]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hnle : n ≤ ramifiedPBWOrder l hl P :=
    Finset.le_sup (f := id) hn
  have hmle : m ≤ ramifiedPBWOrder l hl Q :=
    Finset.le_sup (f := id) hm
  exact ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
    l hl _ _ n m j (by omega)

theorem ramifiedPBWCoeffs_atomCommutator_first_any_second
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m : ℕ) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(n+1)) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^(n+1))) (n+m) =
      f * ((n+1 : ℂ) • ramifiedDerivative l g) -
        g * ((m : ℂ) • ramifiedDerivative l f) := by
  cases m with
  | zero =>
      simpa using ramifiedPBWCoeffs_positive_zero_commutator_next
        l hl f g n
  | succ m =>
      simpa only [Nat.add_assoc, Nat.cast_succ] using
        ramifiedPBWCoeffs_atomCommutator_next l hl f g n m

/-- At the top Laurent exponent, every first-contraction atom pair has
the same determinant formula, including the order-zero boundary. -/
theorem ramifiedPBWCoeffs_atomCommutator_first_extremal
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (i u : ℤ) (n m : ℕ)
    (hf : LaurentUpper f i) (hg : LaurentUpper g u)
    (hfi : i ∈ f.coeff.support) (hgu : u ∈ g.coeff.support) :
    (ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^(n+1)) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^(n+1)))
      (n+m)).coeff (i+u-(l : ℤ)) =
      (((n+1 : ℂ) * (u : ℂ) - (m : ℂ) * (i : ℂ)) /
        (l : ℂ)) * f.coeff i * g.coeff u := by
  rw [ramifiedPBWCoeffs_atomCommutator_first_any_second]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ramified_first_contraction_extremal_coeff l f g i u
      (n+1) m hf hg hfi hgu)

end Dixmier.Weyl
