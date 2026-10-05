/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstFaceCanonical
public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax
public import DixmierFormal.Weyl.RamifiedEndpointCoefficient

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Determinant coefficients on the first ramified commutator face

This identifies each surviving top-atom contribution with its commutative
Poisson determinant. The sum is finite and has no differential-order cutoff.
-/

set_option maxHeartbeats 0

namespace Dixmier.Weyl

/-- At the exact first-contraction weight, the Laurent exponent is
forced to be the sum of the two top exponents minus the ramification
index. The coefficient is the usual Poisson determinant. -/
theorem ramified_first_face_top_atom_determinant
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (f g : LaurentPolynomial ℂ) (B C A D : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (hfi : B ∈ f.coeff.support) (hgu : C ∈ g.coeff.support)
    (n m j : ℕ) (hfirst : n+m=j+1)
    (hPtop : ρ*B + (l : ℤ)*σ*(n : ℤ) = A)
    (hQtop : ρ*C + (l : ℤ)*σ*(m : ℤ) = D)
    (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      A+D-(l : ℤ)*(ρ+σ)) :
    (f * ((n : ℂ) • ramifiedDerivative l g) -
      g * ((m : ℂ) • ramifiedDerivative l f)).coeff v =
      (((n : ℂ)*(C : ℂ) - (m : ℂ)*(B : ℂ)) / (l : ℂ)) *
        f.coeff B * g.coeff C := by
  have hfirstZ : (n : ℤ)+(m : ℤ)=(j : ℤ)+1 := by
    exact_mod_cast hfirst
  have hfirstMul := congrArg (fun z : ℤ => (l : ℤ)*σ*z) hfirstZ
  have hvcoord : v = B+C-(l : ℤ) := by
    dsimp [ramifiedWeight] at hv
    nlinarith [hfirstMul]
  rw [hvcoord]
  exact ramified_first_contraction_extremal_coeff l f g B C n m
    hf hg hfi hgu

/-- On the exact first-contraction face, the full commutator has the
coefficientwise Poisson determinant of the two actual top faces. The
sum is over arbitrary finite PBW expansions, with no order cutoff. -/
theorem ramifiedPBWCoeffs_commutator_first_face_determinant
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      ∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
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
          else 0 := by
  classical
  have hbound : ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q -
      (l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j) := by
    rw [hv]
  rw [ramifiedPBWCoeffs_commutator_first_face_canonical
    l hl ρ σ hρ hsum P Q hPne hQne j v hbound]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hfirst : n+m=j+1
  · by_cases htopP : ρ*ramifiedPBWTopLaurent l hl P n +
        (l : ℤ)*σ*(n : ℤ) = ramifiedWeightDeg l hl ρ σ P
    · by_cases htopQ : ρ*ramifiedPBWTopLaurent l hl Q m +
          (l : ℤ)*σ*(m : ℤ) = ramifiedWeightDeg l hl ρ σ Q
      · have heq := ramified_first_face_top_atom_determinant
          l hl ρ σ hρ _ _
          (ramifiedPBWTopLaurent l hl P n)
          (ramifiedPBWTopLaurent l hl Q m)
          (ramifiedWeightDeg l hl ρ σ P)
          (ramifiedWeightDeg l hl ρ σ Q)
          (ramifiedPBWTopLaurent_upper l hl P n)
          (ramifiedPBWTopLaurent_upper l hl Q m)
          (ramifiedPBWTopLaurent_mem l hl P n hn)
          (ramifiedPBWTopLaurent_mem l hl Q m hm)
          n m j hfirst htopP htopQ v hv
        simpa only [hfirst, htopP, htopQ, true_and,
          and_true, ↓reduceIte] using heq
      · simp [hfirst, htopP, htopQ]
    · simp [hfirst, htopP]
  · simp [hfirst]

end Dixmier.Weyl
