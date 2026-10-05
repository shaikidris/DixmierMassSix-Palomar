/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical leading-face endpoints of an exact ramified Weyl pair

This is the consumer-facing connection between actual finite PBW
support and the no-cancellation determinant theorem. The exceptional
output-order-zero boundary remains explicit.
-/

namespace Dixmier.Weyl

theorem exists_ramified_exact_pair_canonical_face_endpoints
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : P*Q-Q*P = 1) :
    ∃ (N M : ℕ),
      N ∈ (ramifiedPBWCoeffs l hl P).support ∧
      M ∈ (ramifiedPBWCoeffs l hl Q).support ∧
      ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl P N,N) =
        ramifiedWeightDeg l hl ρ σ P ∧
      ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl Q M,M) =
        ramifiedWeightDeg l hl ρ σ Q ∧
      (∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
        ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl P a,a) =
          ramifiedWeightDeg l hl ρ σ P → a ≤ N) ∧
      (∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
        ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl Q b,b) =
          ramifiedWeightDeg l hl ρ σ Q → b ≤ M) ∧
      (0 < N ∧ 1 < N+M →
        (N : ℂ) * ((ramifiedPBWTopLaurent l hl Q M : ℤ) : ℂ) -
          (M : ℂ) * ((ramifiedPBWTopLaurent l hl P N : ℤ) : ℂ) = 0) := by
  obtain ⟨hPS,hQS⟩ :=
    ramified_exact_pair_support_nonempty l hl P Q hcomm
  obtain ⟨A,N,hN,hPupper,hNtop,hNmax,hNi,hPdeg⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ P hPS
  obtain ⟨D,M,hM,hQupper,hMtop,hMmax,hMi,hQdeg⟩ :=
    exists_ramified_canonical_face_endpoint l hl ρ σ hρ Q hQS
  refine ⟨N,M,hN,hM,?_,?_,?_,?_,?_⟩
  · simpa [ramifiedWeight, hPdeg] using hNtop
  · simpa [ramifiedWeight, hQdeg] using hMtop
  · intro a ha haTop
    apply hNmax a ha
    simpa [ramifiedWeight, hPdeg] using haTop
  · intro b hb hbTop
    apply hMmax b hb
    simpa [ramifiedWeight, hQdeg] using hbTop
  · rintro ⟨hNpos,hSumpos⟩
    cases N with
    | zero => omega
    | succ n =>
        have hout : 0 < n+M := by omega
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
          (ramified_exact_pair_face_endpoint_determinant_zero
            l hl ρ σ hρ hsum P Q
            (ramifiedPBWTopLaurent l hl P)
            (ramifiedPBWTopLaurent l hl Q)
            A D n M hcomm hout hN hM
            (fun a _ => ramifiedPBWTopLaurent_upper l hl P a)
            (fun b _ => ramifiedPBWTopLaurent_upper l hl Q b)
            hPupper hQupper hNmax hMmax hNtop hMtop hNi hMi)

end Dixmier.Weyl
