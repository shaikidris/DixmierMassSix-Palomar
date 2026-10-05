/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFullWeightFilter
public import DixmierFormal.Weyl.RamifiedFirstSlopeSymmetry
public import DixmierFormal.Weyl.RamifiedFirstCoefficientAll

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First PBW contraction for every pair of ramified atoms

The existing first-contraction theorem takes the left atom to have
positive derivative order. A full finite Poisson-face sum also has
terms with left order zero. The reversed commutator supplies that
boundary case without restricting the right order.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_atomCommutator_first_all
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m : ℕ)
    (hpos : 0 < n+m) :
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) (n+m-1) =
      f * ((n : ℂ) • ramifiedDerivative l g) -
        g * ((m : ℂ) • ramifiedDerivative l f) := by
  cases n with
  | succ k =>
      simpa [Nat.succ_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ramifiedPBWCoeffs_atomCommutator_first_any_second
          l hl f g k m
  | zero =>
      cases m with
      | zero => omega
      | succ k =>
          have hswap := ramifiedPBWCoeffs_atomCommutator_first_any_second
            l hl g f k 0
          have hneg :
              (ramifiedCoeffGen l f * (ramifiedYGen l)^0) *
                  (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) -
                (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) *
                  (ramifiedCoeffGen l f * (ramifiedYGen l)^0) =
              -((ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1)) *
                  (ramifiedCoeffGen l f * (ramifiedYGen l)^0) -
                (ramifiedCoeffGen l f * (ramifiedYGen l)^0) *
                  (ramifiedCoeffGen l g * (ramifiedYGen l)^(k+1))) := by
            abel
          rw [hneg, ramifiedPBWCoeffs_neg, Finsupp.neg_apply]
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            congrArg Neg.neg hswap

/-- At the first-contraction weight of a full finite ramified
commutator, every surviving atom pair has exactly one contraction.
This is an all-orders coefficient formula, including order-zero atoms.
The Newton bounds make all later contractions vanish at the selected
coefficient. -/
theorem ramifiedPBWCoeffs_commutator_first_face_coefficient
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ) (j : ℕ) (v : ℤ)
    (hBP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) n) (B n))
    (hCQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) m) (C m))
    (hP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B n) + (l : ℤ)*σ*(n : ℤ) ≤ A)
    (hQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C m) + (l : ℤ)*σ*(m : ℤ) ≤ D)
    (hv : A+D-(l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      ∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
          if n+m = j+1 then
            ( (ramifiedPBWCoeffs l hl P) n *
                ((n : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl Q) m)) -
              (ramifiedPBWCoeffs l hl Q) m *
                ((m : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl P) n)) ).coeff v
          else 0 := by
  classical
  rw [ramifiedPBWCoeffs_commutator_double_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hfirst : n+m = j+1
  · simp only [hfirst, ↓reduceIte]
    have hpos : 0 < n+m := by omega
    have hidx : j = n+m-1 := by omega
    rw [hidx, ramifiedPBWCoeffs_atomCommutator_first_all l hl _ _ n m hpos]
  · simp only [hfirst, ↓reduceIte]
    by_cases hlow : n+m ≤ j
    · rw [ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
        l hl _ _ n m j hlow]
      simp
    · have hmore : j+2 ≤ n+m := by omega
      by_contra hnz
      have hmem : v ∈
          (ramifiedPBWCoeffs l hl
            ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
                (ramifiedYGen l)^n) *
                (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
                  (ramifiedYGen l)^m) -
              (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
                (ramifiedYGen l)^m) *
                (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
                  (ramifiedYGen l)^n)) j).coeff.support :=
        Finsupp.mem_support_iff.mpr hnz
      have hbelow := ramifiedPBWCoeffs_atomCommutator_below_first_of_defect_all
        l hl ρ σ hρ hsum _ _ (B n) (C m) A D
        (hBP n hn) (hCQ m hm) n m j (by omega)
        (hP n hn) (hQ m hm) (Or.inr (Or.inr hmore)) v hmem
      omega

end Dixmier.Weyl
