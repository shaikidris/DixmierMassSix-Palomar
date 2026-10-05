/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedConstantEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact Weyl criterion at the maximal Newton-face endpoint

The determinant of the two maximal face endpoints is nonzero exactly
when their first-contraction output is the constant PBW monomial.
This is the exact-pair, maximal-endpoint interface needed from the
end-point part of G13 Proposition 2.4.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_face_endpoint_nonparallel_iff_constant
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ) (n m : ℕ)
    (hcomm : P*Q-Q*P = 1)
    (hN : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hM : m ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hBP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) a) (B a))
    (hCQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) b) (C b))
    (hP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) ≤ A)
    (hQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) ≤ D)
    (hNmax : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) = A → a ≤ n+1)
    (hMmax : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) = D → b ≤ m)
    (hNtop : ρ*(B (n+1)) + (l : ℤ)*σ*((n+1 : ℕ) : ℤ) = A)
    (hMtop : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D)
    (hfi : B (n+1) ∈
      ((ramifiedPBWCoeffs l hl P) (n+1)).coeff.support)
    (hgu : C m ∈ ((ramifiedPBWCoeffs l hl Q) m).coeff.support) :
    ((n+1 : ℂ) * ((C m : ℤ) : ℂ) -
      (m : ℂ) * ((B (n+1) : ℤ) : ℂ) ≠ 0) ↔
      n+m = 0 ∧ B (n+1)+C m = (l : ℤ) := by
  let det : ℂ :=
    (n+1 : ℂ) * ((C m : ℤ) : ℂ) -
      (m : ℂ) * ((B (n+1) : ℤ) : ℂ)
  let a : ℂ := ((ramifiedPBWCoeffs l hl P) (n+1)).coeff (B (n+1))
  let b : ℂ := ((ramifiedPBWCoeffs l hl Q) m).coeff (C m)
  have hcoeff := ramifiedPBWCoeffs_face_endpoint_extremal
    l hl ρ σ hρ hsum P Q B C A D n m
    hN hM hBP hCQ hP hQ hNmax hMmax hNtop hMtop hfi hgu
  have hlne : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  have hbase := ramified_exact_pair_determinant_nonzero_iff_origin
    l hl P Q hcomm (n+m) (B (n+1)+C m-(l : ℤ))
    (det/(l : ℂ)) a b
    (Finsupp.mem_support_iff.mp hfi)
    (Finsupp.mem_support_iff.mp hgu) hcoeff
  change det ≠ 0 ↔ n+m = 0 ∧ B (n+1)+C m = (l : ℤ)
  constructor
  · intro hd
    have hdiv : det/(l : ℂ) ≠ 0 := div_ne_zero hd hlne
    obtain ⟨hj,hv⟩ := hbase.mp hdiv
    exact ⟨hj,by omega⟩
  · rintro ⟨hj,hv⟩
    have hpoint : n+m = 0 ∧ B (n+1)+C m-(l : ℤ) = 0 :=
      ⟨hj,by omega⟩
    have hdiv := hbase.mpr hpoint
    intro hd
    exact hdiv (by simp [hd])

end Dixmier.Weyl
