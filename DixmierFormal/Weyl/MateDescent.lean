/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Fourier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact mate subtraction

The mate descent in the paper repeatedly replaces `Q` by `Q - c • P^k`.
These identities use the exact Weyl multiplication and do not depend on a
leading-symbol approximation or on the published Newton inputs.
-/

namespace Dixmier.Weyl

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem mateSubtraction_commutator (P Q : A1 K) (c : K) (k : ℕ) :
    (Q - c • P ^ k) * P - P * (Q - c • P ^ k) = Q * P - P * Q := by
  have hcomm : (c • P ^ k) * P = P * (c • P ^ k) := by
    rw [smul_mul_assoc, mul_smul_comm]
    rw [← pow_succ, ← pow_succ']
  rw [sub_mul Q (c • P ^ k) P, mul_sub P Q (c • P ^ k), hcomm]
  abel

set_option maxHeartbeats 1000000 in
omit [CharZero K] in
theorem mateSubtraction_adjoin (P Q : A1 K) (c : K) (k : ℕ) :
    Algebra.adjoin K ({P, Q - c • P ^ k} : Set (A1 K)) =
      Algebra.adjoin K ({P, Q} : Set (A1 K)) := by
  let S := Algebra.adjoin K ({P, Q} : Set (A1 K))
  let T := Algebra.adjoin K ({P, Q - c • P ^ k} : Set (A1 K))
  have hPS : P ∈ S := Algebra.subset_adjoin (by simp)
  have hQS : Q ∈ S := Algebra.subset_adjoin (by simp)
  have hPT : P ∈ T := Algebra.subset_adjoin (by simp)
  have hQT : Q - c • P ^ k ∈ T := Algebra.subset_adjoin (by simp)
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro x hx
    change x ∈ S
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · simpa only [hx] using hPS
    · have hsub : Q - c • P ^ k ∈ S :=
        Subalgebra.sub_mem (R := K) (A := A1 K) S hQS
          (S.smul_mem (S.pow_mem hPS k) c)
      simpa only [hx] using hsub
  · apply Algebra.adjoin_le
    intro x hx
    change x ∈ T
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · simpa only [hx] using hPT
    ·
      have hsum : (Q - c • P ^ k) + c • P ^ k ∈ T :=
        T.add_mem hQT (T.smul_mem (T.pow_mem hPT k) c)
      have heq : (Q - c • P ^ k) + c • P ^ k = Q := sub_add_cancel Q _
      have hQ : Q ∈ T := heq ▸ hsum
      simpa only [hx] using hQ

theorem isCounterexamplePair_mateSubtraction (P Q : A1 ℂ) (c : ℂ) (k : ℕ)
    (h : IsCounterexamplePair P Q) :
    IsCounterexamplePair P (Q - c • P ^ k) := by
  constructor
  · rw [mateSubtraction_commutator]
    exact h.1
  · rw [mateSubtraction_adjoin]
    exact h.2

end Dixmier.Weyl
