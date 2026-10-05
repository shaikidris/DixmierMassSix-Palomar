/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedConstantEndpoint
public import DixmierFormal.Weyl.RamifiedFullWeightFilter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact commutators require enough total Newton weight

The constant PBW coefficient of an exact Weyl commutator forces the
sum of the two upper Newton weights to reach the first-contraction
weight step. The proof uses the unrestricted finite PBW double sum.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_weight_sum_lower
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ)
    (hcomm : P*Q-Q*P = 1)
    (hBP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) n) (B n))
    (hCQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) m) (C m))
    (hP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B n) + (l : ℤ)*σ*(n : ℤ) ≤ A)
    (hQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C m) + (l : ℤ)*σ*(m : ℤ) ≤ D) :
    (l : ℤ)*(ρ+σ) ≤ A+D := by
  by_contra hbad
  have hlt : A+D < (l : ℤ)*(ρ+σ) := by omega
  let A' : ℤ := (l : ℤ)*(ρ+σ)-D
  have hP' : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B n) + (l : ℤ)*σ*(n : ℤ) ≤ A' := by
    intro n hn
    have hp := hP n hn
    dsimp [A']
    omega
  have hv : A'+D-(l : ℤ)*(ρ+σ) ≤
      ramifiedWeight l ρ σ ((0 : ℤ),0) := by
    simp [A', ramifiedWeight]
  have hnz : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) 0).coeff 0 ≠ 0 := by
    rw [hcomm, ramifiedPBWCoeffs_one_coeff_at_origin]
    exact one_ne_zero
  obtain ⟨n,hn,m,hm,_,hpEq,_⟩ :=
    ramifiedPBWCoeffs_commutator_first_weight_survivor
      l hl ρ σ hρ hsum P Q B C A' D 0 0
      hBP hCQ hP' hQ hv hnz
  have hp := hP n hn
  dsimp [A'] at hpEq
  omega

/-- The same lower bound for the *actual* attained Newton degrees of
an exact finite ramified Weyl pair. In particular, both degrees cannot
be zero at a positive-sum direction. -/
theorem ramified_exact_pair_weightDeg_sum_lower
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : P*Q-Q*P = 1) :
    (l : ℤ)*(ρ+σ) ≤
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q := by
  obtain ⟨hPS,hQS⟩ := ramified_exact_pair_support_nonempty l hl P Q hcomm
  obtain ⟨A,N,hN,hP,hNtop,hNmax,hNi,hAdeg⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ P hPS
  obtain ⟨D,M,hM,hQ,hMtop,hMmax,hMi,hDdeg⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ Q hQS
  have hbound := ramified_exact_pair_weight_sum_lower
    l hl ρ σ hρ hsum P Q
      (ramifiedPBWTopLaurent l hl P)
      (ramifiedPBWTopLaurent l hl Q)
      A D hcomm
      (fun n _ => ramifiedPBWTopLaurent_upper l hl P n)
      (fun m _ => ramifiedPBWTopLaurent_upper l hl Q m)
      hP hQ
  rw [hAdeg,hDdeg]
  exact hbound

end Dixmier.Weyl
