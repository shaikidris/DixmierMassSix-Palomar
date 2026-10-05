/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutCanonicalStart

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Constant-output criterion in the paper's commutator orientation

The source uses `[Q,P]=1`. Keeping `P` as the first atom in the
first-contraction formula requires the reversed scalar `-1` output.
-/

namespace Dixmier.Weyl

theorem ramified_reversed_pair_coeff_nonzero_iff_origin
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1) (j : ℕ) (v : ℤ) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v ≠ 0 ↔
      j = 0 ∧ v = 0 := by
  have hanti : P*Q-Q*P = -(Q*P-P*Q) := by abel
  have hcoeff : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      -((ramifiedPBWCoeffs l hl (Q*P-P*Q)) j).coeff v := by
    rw [hanti, ← neg_one_smul ℂ (Q*P-P*Q),
      ramifiedPBWCoeffs_smul]
    simp
  rw [hcoeff]
  simpa only [neg_ne_zero] using
    ramified_exact_pair_coeff_nonzero_iff_origin l hl Q P hcomm j v

theorem ramified_reversed_pair_determinant_nonzero_iff_origin
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (j : ℕ) (v : ℤ) (d a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcoeff : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      d*a*b) :
    d ≠ 0 ↔ j = 0 ∧ v = 0 := by
  have horigin := ramified_reversed_pair_coeff_nonzero_iff_origin
    l hl P Q hcomm j v
  constructor
  · intro hd
    apply horigin.mp
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero hd ha) hb
  · intro hpoint
    have hnz := horigin.mpr hpoint
    rw [hcoeff] at hnz
    intro hd
    simp [hd] at hnz

end Dixmier.Weyl
