/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCanonicalFaceMin

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical start endpoints of an exact ramified Weyl pair

The selected endpoints are attained points of the actual finite PBW
support. When the first endpoint has positive derivative order, the
full commutator gives the exact constant-output criterion.
-/

namespace Dixmier.Weyl

theorem exists_ramified_exact_pair_canonical_face_starts
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
          ramifiedWeightDeg l hl ρ σ P → N ≤ a) ∧
      (∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
        ramifiedWeight l ρ σ (ramifiedPBWTopLaurent l hl Q b,b) =
          ramifiedWeightDeg l hl ρ σ Q → M ≤ b) ∧
      (0 < N →
        (((N : ℂ) * ((ramifiedPBWTopLaurent l hl Q M : ℤ) : ℂ) -
          (M : ℂ) * ((ramifiedPBWTopLaurent l hl P N : ℤ) : ℂ) ≠ 0) ↔
          N+M = 1 ∧
            ramifiedPBWTopLaurent l hl P N +
              ramifiedPBWTopLaurent l hl Q M = (l : ℤ))) := by
  obtain ⟨hPS,hQS⟩ :=
    ramified_exact_pair_support_nonempty l hl P Q hcomm
  obtain ⟨A,N,hN,hPupper,hNtop,hNmin,hNi,hPdeg⟩ :=
    exists_ramified_canonical_face_start l hl ρ σ hρ P hPS
  obtain ⟨D,M,hM,hQupper,hMtop,hMmin,hMi,hQdeg⟩ :=
    exists_ramified_canonical_face_start l hl ρ σ hρ Q hQS
  refine ⟨N,M,hN,hM,?_,?_,?_,?_,?_⟩
  · simpa [ramifiedWeight, hPdeg] using hNtop
  · simpa [ramifiedWeight, hQdeg] using hMtop
  · intro a ha haTop
    apply hNmin a ha
    simpa [ramifiedWeight, hPdeg] using haTop
  · intro b hb hbTop
    apply hMmin b hb
    simpa [ramifiedWeight, hQdeg] using hbTop
  · intro hNpos
    cases N with
    | zero => omega
    | succ n =>
        have hcriterion :=
          ramified_exact_pair_face_start_nonparallel_iff_constant
            l hl ρ σ hρ hsum P Q
            (ramifiedPBWTopLaurent l hl P)
            (ramifiedPBWTopLaurent l hl Q)
            A D n M hcomm hN hM
            (fun a _ => ramifiedPBWTopLaurent_upper l hl P a)
            (fun b _ => ramifiedPBWTopLaurent_upper l hl Q b)
            hPupper hQupper hNmin hMmin hNtop hMtop hNi hMi
        have hNat : n+M = 0 ↔ n+1+M = 1 := by omega
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
          ← hNat] using
          hcriterion

end Dixmier.Weyl
