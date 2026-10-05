/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstFaceBracket

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Top-weight pairs in the ramified first-contraction coefficient

Only pairs of atoms on the two original top faces contribute to the
first-contraction coefficient at its predicted Newton weight.
-/

set_option maxHeartbeats 0

namespace Dixmier.Weyl

/-- At the first-contraction threshold, an atom below either input's
top weight cannot contribute. -/
theorem ramified_first_face_atom_coeff_zero_of_lower_weight
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (f g : LaurentPolynomial ℂ) (B C A D : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m j : ℕ) (hfirst : n + m = j + 1)
    (hP : ρ*B + (l : ℤ)*σ*(n : ℤ) ≤ A)
    (hQ : ρ*C + (l : ℤ)*σ*(m : ℤ) ≤ D)
    (hdefect : ρ*B + (l : ℤ)*σ*(n : ℤ) < A ∨
      ρ*C + (l : ℤ)*σ*(m : ℤ) < D)
    (v : ℤ)
    (hv : A + D - (l : ℤ)*(ρ + σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    (f * ((n : ℂ) • ramifiedDerivative l g) -
      g * ((m : ℂ) • ramifiedDerivative l f)).coeff v = 0 := by
  have hidx : j = n + m - 1 := by omega
  have hcomm :
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
            (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
            (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j).coeff v =
        (f * ((n : ℂ) • ramifiedDerivative l g) -
          g * ((m : ℂ) • ramifiedDerivative l f)).coeff v := by
    rw [hidx, ramifiedPBWCoeffs_atomCommutator_first_all l hl f g n m (by omega)]
  by_contra hnz
  have hmem : v ∈
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
            (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
            (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j).coeff.support :=
    Finsupp.mem_support_iff.mpr (by rw [hcomm]; exact hnz)
  have hbelow := ramifiedPBWCoeffs_atomCommutator_below_first_of_defect_all
    l hl ρ σ hρ hsum f g B C A D hf hg n m j (by omega)
    hP hQ (hdefect.elim Or.inl (fun h => Or.inr (Or.inl h))) v hmem
  omega

/-- The top coefficient of an unrestricted finite ramified commutator
depends only on first contractions between top-weight PBW atoms. -/
theorem ramifiedPBWCoeffs_commutator_first_face_top_pairs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
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
    (hv : A + D - (l : ℤ)*(ρ + σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      ∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
          if n+m = j+1 ∧
              ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A ∧
              ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D then
            ((ramifiedPBWCoeffs l hl P) n *
                ((n : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl Q) m)) -
              (ramifiedPBWCoeffs l hl Q) m *
                ((m : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl P) n))).coeff v
          else 0 := by
  classical
  rw [ramifiedPBWCoeffs_commutator_first_face_coefficient
    l hl ρ σ hρ hsum P Q B C A D j v hBP hCQ hP hQ hv]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hfirst : n+m = j+1
  · by_cases hp : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A
    · by_cases hq : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D
      · simp [hfirst, hp, hq]
      · have hqstrict : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D := by
          have := hQ m hm
          omega
        have hz := ramified_first_face_atom_coeff_zero_of_lower_weight
          l hl ρ σ hρ hsum _ _ (B n) (C m) A D
          (hBP n hn) (hCQ m hm) n m j hfirst
          (hP n hn) (hQ m hm) (Or.inr hqstrict) v hv
        simpa only [hfirst, hp, hq, true_and, and_true,
          false_and, and_false, ↓reduceIte] using hz
    · have hpstrict : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A := by
        have := hP n hn
        omega
      have hz := ramified_first_face_atom_coeff_zero_of_lower_weight
        l hl ρ σ hρ hsum _ _ (B n) (C m) A D
        (hBP n hn) (hCQ m hm) n m j hfirst
        (hP n hn) (hQ m hm) (Or.inl hpstrict) v hv
      simpa only [hfirst, hp, true_and, and_true,
        false_and, and_false, ↓reduceIte] using hz
  · simp [hfirst]

end Dixmier.Weyl
