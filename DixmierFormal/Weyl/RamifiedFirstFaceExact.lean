/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstFaceDeterminant
public import DixmierFormal.Weyl.RamifiedConstantEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First-face determinant vanishing for an exact ramified pair

The commutator-one relation annihilates every positive-weight
coefficient of the first contraction face.
-/

namespace Dixmier.Weyl

/-- For an exact ramified Weyl pair, every positive-weight coefficient
of the first commutator face has zero Poisson-determinant sum. This is
the pointwise vanishing needed before constructing a companion form. -/
theorem ramified_exact_pair_first_face_determinant_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ))
    (hpositive : 0 < ramifiedWeight l ρ σ (v,j)) :
      (∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
          if n+m = j+1 ∧
              ρ*ramifiedPBWTopLaurent l hl P n +
                (l : ℤ)*σ*(n : ℤ) = ramifiedWeightDeg l hl ρ σ P ∧
              ρ*ramifiedPBWTopLaurent l hl Q m +
                (l : ℤ)*σ*(m : ℤ) = ramifiedWeightDeg l hl ρ σ Q then
            (((n : ℂ)*(ramifiedPBWTopLaurent l hl Q m : ℂ) -
                (m : ℂ)*(ramifiedPBWTopLaurent l hl P n : ℂ)) /
                  (l : ℂ)) *
              ((ramifiedPBWCoeffs l hl P) n).coeff
                (ramifiedPBWTopLaurent l hl P n) *
              ((ramifiedPBWCoeffs l hl Q) m).coeff
                (ramifiedPBWTopLaurent l hl Q m)
          else 0) = 0 := by
  have heq := ramifiedPBWCoeffs_commutator_first_face_determinant
    l hl ρ σ hρ hsum P Q hPne hQne j v hv
  rw [← heq]
  by_contra hne
  have horigin := (ramified_exact_pair_coeff_nonzero_iff_origin
    l hl P Q hcomm j v).mp hne
  rcases horigin with ⟨rfl,rfl⟩
  simp [ramifiedWeight] at hpositive

end Dixmier.Weyl
