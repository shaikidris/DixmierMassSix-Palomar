/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstFaceTopPairs
public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First commutator face from canonical Newton maxima

The top-pair filter is instantiated with actual finite ramified PBW supports.
-/

namespace Dixmier.Weyl

/-- The exact first-contraction coefficient of a finite ramified
commutator uses only the actual top Newton atoms of its two inputs.
All upper exponents and top weights are canonical, with no order bound. -/
theorem ramifiedPBWCoeffs_commutator_first_face_canonical
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      ∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
          if n+m = j+1 ∧
              ρ*ramifiedPBWTopLaurent l hl P n +
                (l : ℤ)*σ*(n : ℤ) = ramifiedWeightDeg l hl ρ σ P ∧
              ρ*ramifiedPBWTopLaurent l hl Q m +
                (l : ℤ)*σ*(m : ℤ) = ramifiedWeightDeg l hl ρ σ Q then
            ((ramifiedPBWCoeffs l hl P) n *
                ((n : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl Q) m)) -
              (ramifiedPBWCoeffs l hl Q) m *
                ((m : ℂ) • ramifiedDerivative l
                  ((ramifiedPBWCoeffs l hl P) n))).coeff v
          else 0 := by
  have hSP := ramifiedPBWSupport_nonempty_of_ne_zero l hl P hPne
  have hSQ := ramifiedPBWSupport_nonempty_of_ne_zero l hl Q hQne
  obtain ⟨A, _, _, hPB, _, _, _, hA⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ P hSP
  obtain ⟨D, _, _, hQC, _, _, _, hD⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ Q hSQ
  have hv' : A + D - (l : ℤ)*(ρ+σ) ≤
      ramifiedWeight l ρ σ (v,j) := by
    rw [hA,hD] at hv
    exact hv
  have htop := ramifiedPBWCoeffs_commutator_first_face_top_pairs
    l hl ρ σ hρ hsum P Q
    (ramifiedPBWTopLaurent l hl P)
    (ramifiedPBWTopLaurent l hl Q)
    A D j v
    (by intro n hn; exact ramifiedPBWTopLaurent_upper l hl P n)
    (by intro m hm; exact ramifiedPBWTopLaurent_upper l hl Q m)
    hPB hQC hv'
  rw [← hA, ← hD] at htop
  exact htop

end Dixmier.Weyl
