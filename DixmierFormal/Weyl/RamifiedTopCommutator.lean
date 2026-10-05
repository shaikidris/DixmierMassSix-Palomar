/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstCoefficientAll

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The first nontrivial PBW coefficient of a full commutator

At derivative order one below the sum of the operator orders, every
atom pair except the two top-order atoms vanishes. This is an exact
finite-sum statement for operators of arbitrary order.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_commutator_top_next
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) (n m : ℕ)
    (hP : ramifiedPBWOrder l hl P = n+1)
    (hQ : ramifiedPBWOrder l hl Q = m)
    (hPn : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hQm : m ∈ (ramifiedPBWCoeffs l hl Q).support) :
    ramifiedPBWCoeffs l hl (P*Q-Q*P) (n+m) =
      (ramifiedPBWCoeffs l hl P) (n+1) *
          ((n+1 : ℂ) • ramifiedDerivative l
            ((ramifiedPBWCoeffs l hl Q) m)) -
        (ramifiedPBWCoeffs l hl Q) m *
          ((m : ℂ) • ramifiedDerivative l
            ((ramifiedPBWCoeffs l hl P) (n+1))) := by
  rw [ramifiedPBWCoeffs_commutator_double_sum]
  rw [Finset.sum_eq_single (n+1)]
  · rw [Finset.sum_eq_single m]
    · exact ramifiedPBWCoeffs_atomCommutator_first_any_second
        l hl _ _ n m
    · intro k hk hkm
      have hkbound : k ≤ m := by
        rw [← hQ]
        exact Finset.le_sup (f := id) hk
      exact ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
        l hl _ _ (n+1) k (n+m) (by omega)
    · intro hmnot
      exact False.elim (hmnot hQm)
  · intro j hj hjeq
    apply Finset.sum_eq_zero
    intro k hk
    have hjbound : j ≤ n+1 := by
      rw [← hP]
      exact Finset.le_sup (f := id) hj
    have hkbound : k ≤ m := by
      rw [← hQ]
      exact Finset.le_sup (f := id) hk
    exact ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
      l hl _ _ j k (n+m) (by omega)
  · intro hnot
    exact False.elim (hnot hPn)

/-- The extremal Laurent coefficient of the full operator commutator
is the determinant of the two top PBW endpoint exponents. Lower
derivative-order atoms cannot cancel it. -/
theorem ramifiedPBWCoeffs_commutator_top_next_extremal
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) (n m : ℕ) (i u : ℤ)
    (hP : ramifiedPBWOrder l hl P = n+1)
    (hQ : ramifiedPBWOrder l hl Q = m)
    (hPn : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hQm : m ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hf : LaurentUpper ((ramifiedPBWCoeffs l hl P) (n+1)) i)
    (hg : LaurentUpper ((ramifiedPBWCoeffs l hl Q) m) u)
    (hfi : i ∈ ((ramifiedPBWCoeffs l hl P) (n+1)).coeff.support)
    (hgu : u ∈ ((ramifiedPBWCoeffs l hl Q) m).coeff.support) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) (n+m)).coeff
        (i+u-(l : ℤ)) =
      (((n+1 : ℂ) * (u : ℂ) - (m : ℂ) * (i : ℂ)) /
        (l : ℂ)) *
        ((ramifiedPBWCoeffs l hl P) (n+1)).coeff i *
        ((ramifiedPBWCoeffs l hl Q) m).coeff u := by
  rw [ramifiedPBWCoeffs_commutator_top_next l hl P Q n m
    hP hQ hPn hQm]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ramified_first_contraction_extremal_coeff l
      ((ramifiedPBWCoeffs l hl P) (n+1))
      ((ramifiedPBWCoeffs l hl Q) m) i u (n+1) m
      hf hg hfi hgu)

theorem ramifiedPBWCoeffs_one_at_positive_order
    (l : ℕ) (hl : 0 < l) (j : ℕ) (hj : 0 < j) :
    ramifiedPBWCoeffs l hl (1 : ramifiedOperatorAlgebra l) j = 0 := by
  have hone : (1 : ramifiedOperatorAlgebra l) =
      ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one.symm
  rw [hone, ramifiedPBWCoeffs_coeffGen]
  simp [Finsupp.single_eq_of_ne (by omega : j ≠ 0)]

/-- For an exact ramified Weyl pair of positive combined top order,
the leading Laurent exponents of the top derivative coefficients
satisfy the first-contraction determinant equation. -/
theorem ramified_exact_pair_top_endpoint_determinant_zero
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) (n m : ℕ) (i u : ℤ)
    (hcomm : P*Q-Q*P = 1)
    (hpositive : 0 < n+m)
    (hP : ramifiedPBWOrder l hl P = n+1)
    (hQ : ramifiedPBWOrder l hl Q = m)
    (hPn : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hQm : m ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hf : LaurentUpper ((ramifiedPBWCoeffs l hl P) (n+1)) i)
    (hg : LaurentUpper ((ramifiedPBWCoeffs l hl Q) m) u)
    (hfi : i ∈ ((ramifiedPBWCoeffs l hl P) (n+1)).coeff.support)
    (hgu : u ∈ ((ramifiedPBWCoeffs l hl Q) m).coeff.support) :
    (n+1 : ℂ) * (u : ℂ) - (m : ℂ) * (i : ℂ) = 0 := by
  have hcoeff := ramifiedPBWCoeffs_commutator_top_next_extremal
    l hl P Q n m i u hP hQ hPn hQm hf hg hfi hgu
  have hz : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) (n+m)).coeff
      (i+u-(l : ℤ)) = 0 := by
    rw [hcomm, ramifiedPBWCoeffs_one_at_positive_order l hl (n+m) hpositive]
    simp
  rw [hz] at hcoeff
  have hfi_ne : ((ramifiedPBWCoeffs l hl P) (n+1)).coeff i ≠ 0 :=
    Finsupp.mem_support_iff.mp hfi
  have hgu_ne : ((ramifiedPBWCoeffs l hl Q) m).coeff u ≠ 0 :=
    Finsupp.mem_support_iff.mp hgu
  have hl_ne : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  rcases mul_eq_zero.mp hcoeff.symm with hleft | hright
  · rcases mul_eq_zero.mp hleft with hdiv | hfi_zero
    · exact (div_eq_zero_iff).mp hdiv |>.resolve_right hl_ne
    · exact False.elim (hfi_ne hfi_zero)
  · exact False.elim (hgu_ne hright)

end Dixmier.Weyl
