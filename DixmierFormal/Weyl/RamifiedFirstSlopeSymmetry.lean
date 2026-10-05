/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstSlopeAlignment

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Reverse the exact-pair first-slope ordering

Negation preserves finite PBW support and converts `[Q,P]=1` into
`[-P,Q]=1`. This transfers the earlier-first-slope contradiction to
the other member without imposing a mate cutoff.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_neg (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (-T) = -ramifiedPBWCoeffs l hl T := by
  calc
    ramifiedPBWCoeffs l hl (-T) =
        ramifiedPBWCoeffs l hl ((-1 : ℂ) • T) := by
          exact congrArg (ramifiedPBWCoeffs l hl)
            (neg_one_smul ℂ T).symm
    _ = (-1 : ℂ) • ramifiedPBWCoeffs l hl T :=
      ramifiedPBWCoeffs_smul l hl (-1) T
    _ = -ramifiedPBWCoeffs l hl T := by rw [neg_one_smul]

theorem ramifiedPBWSupport_neg (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWSupport l hl (-T) = ramifiedPBWSupport l hl T := by
  ext p
  rcases p with ⟨i,j⟩
  rw [ramifiedPBWSupport_mem_iff, ramifiedPBWSupport_mem_iff]
  simp [ramifiedPBWCoeff, ramifiedPBWCoeffs_neg]

theorem ramified_exact_pair_no_later_first_slope
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F B : ℤ × ℕ) (tP tQ : ℚ)
    (htQ : 0 < tQ)
    (hearly : tQ < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hlt : tQ < tP)
    (hEorder : 2 ≤ E.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBQ : B ∈ ramifiedPBWSupport l hl Q)
    (hBlower : B.2 < F.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hBtie : ((ramifiedWeight l ρ σ B : ℤ) : ℚ) - tQ * (B.2 : ℚ) =
      (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hPoldTop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ)) :
    False := by
  have hcomm' : (-P)*Q-Q*(-P) = 1 := by
    calc
      (-P)*Q-Q*(-P) = -(P*Q)-(-(Q*P)) := by
        apply Subtype.ext
        ext f
        simp
      _ = Q*P-P*Q := by abel
      _ = 1 := hcomm
  have hEneg : E ∈ ramifiedPBWSupport l hl (-P) := by
    rw [ramifiedPBWSupport_neg]
    exact hEP
  have hPoldTopNeg : ∀ p ∈ ramifiedPBWSupport l hl (-P),
      ramifiedWeight l ρ σ p ≤ VP := by
    simpa [ramifiedPBWSupport_neg] using hPoldTop
  have hPfirstNeg : ∀ p ∈ ramifiedPBWSupport l hl (-P),
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ) := by
    simpa [ramifiedPBWSupport_neg] using hPfirst
  exact ramified_exact_pair_no_earlier_first_slope
    l hl ρ σ hρ Q (-P) hcomm' VQ VP F E B tQ tP
    htQ hearly hlt hEorder hOld.symm hFQ hEneg hBQ hBlower
    hFold hEold hQfirst hBtie hPoldTopNeg hPfirstNeg

end Dixmier.Weyl
