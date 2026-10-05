/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedProductWeightAll

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite-sum Newton filter for an exact ramified commutator

This theorem connects the atomwise contraction estimate to the
canonical PBW double sum of two unrestricted finite operators. It
isolates the mathematical condition that at least one first-order
top-weight atom pair must survive at the selected coefficient.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_commutator_weight_defect_zero
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
    (hdefect : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      j+1 ≤ n+m →
        ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A ∨
        ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D ∨
        j+2 ≤ n+m)
    (hv : A+D-(l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v = 0 := by
  rw [ramifiedPBWCoeffs_commutator_double_sum]
  apply ramifiedWeight_double_sum_coeff_zero
    _ _ _ l ρ σ hρ j (A+D-(l : ℤ)*(ρ+σ)) v
  · intro n hn m hm u hu
    have hnz : ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
            (ramifiedYGen l)^n) *
            (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
              (ramifiedYGen l)^m) -
          (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
            (ramifiedYGen l)^m) *
            (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
              (ramifiedYGen l)^n)) j ≠ 0 := by
      intro hz
      simp [hz] at hu
    have hcontraction : j+1 ≤ n+m := by
      by_contra hbad
      have htop : n+m ≤ j := by omega
      exact hnz (ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
        l hl _ _ n m j htop)
    exact ramifiedPBWCoeffs_atomCommutator_below_first_of_defect_all
      l hl ρ σ hρ hsum _ _ (B n) (C m) A D
      (hBP n hn) (hCQ m hm) n m j hcontraction
      (hP n hn) (hQ m hm) (hdefect n hn m hm hcontraction) u hu
  · exact hv

/-- A nonzero coefficient at the selected first-contraction weight
forces a genuine top-weight atom pair with exactly one contraction.
This is the support-level converse of the finite-sum filter. -/
theorem ramifiedPBWCoeffs_commutator_first_weight_survivor
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
    (hv : A+D-(l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j))
    (hnz : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v ≠ 0) :
    ∃ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ∃ m ∈ (ramifiedPBWCoeffs l hl Q).support,
        j+1 = n+m ∧
        ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A ∧
        ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D := by
  classical
  by_contra hnone
  have hdefect : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      j+1 ≤ n+m →
        ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A ∨
        ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D ∨
        j+2 ≤ n+m := by
    intro n hn m hm hcontraction
    by_cases hp : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A
    · exact Or.inl hp
    by_cases hq : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D
    · exact Or.inr (Or.inl hq)
    right
    right
    by_contra hno2
    have hfirst : j+1 = n+m := by omega
    have hpEq : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A := by
      have := hP n hn
      omega
    have hqEq : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D := by
      have := hQ m hm
      omega
    exact hnone ⟨n,hn,m,hm,hfirst,hpEq,hqEq⟩
  exact hnz (ramifiedPBWCoeffs_commutator_weight_defect_zero
    l hl ρ σ hρ hsum P Q B C A D j v
    hBP hCQ hP hQ hdefect hv)

end Dixmier.Weyl
