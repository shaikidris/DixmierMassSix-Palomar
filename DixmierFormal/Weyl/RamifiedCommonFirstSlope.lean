/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFirstSlopeSymmetry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Common first adjacent slope of an exact ramified pair

With genuine first-slope witnesses on both finite supports and the
source root-order lower bounds, neither strict ordering is possible.
This is the paired geometric conclusion used by the Newton cut.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_first_slopes_equal
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F BP BQ : ℤ × ℕ) (tP tQ : ℚ)
    (htP : 0 < tP) (htQ : 0 < tQ)
    (hearlyP : tP < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hearlyQ : tQ < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hEorder : 2 ≤ E.2) (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : BP ∈ ramifiedPBWSupport l hl P)
    (hBQ : BQ ∈ ramifiedPBWSupport l hl Q)
    (hBPlower : BP.2 < E.2) (hBQlower : BQ.2 < F.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hPoldTop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP)
    (hQoldTop : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q ≤ VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ))
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hBPtie : ((ramifiedWeight l ρ σ BP : ℤ) : ℚ) - tP * (BP.2 : ℚ) =
      (VP : ℚ) - tP * (E.2 : ℚ))
    (hBQtie : ((ramifiedWeight l ρ σ BQ : ℤ) : ℚ) - tQ * (BQ.2 : ℚ) =
      (VQ : ℚ) - tQ * (F.2 : ℚ)) :
    tP = tQ := by
  rcases lt_trichotomy tP tQ with hlt | heq | hgt
  · exact False.elim (ramified_exact_pair_no_earlier_first_slope
      l hl ρ σ hρ P Q hcomm VP VQ E F BP tP tQ
      htP hearlyP hlt hForder hOld hEP hFQ hBP hBPlower
      hEold hFold hPfirst hBPtie hQoldTop hQfirst)
  · exact heq
  · exact False.elim (ramified_exact_pair_no_later_first_slope
      l hl ρ σ hρ P Q hcomm VP VQ E F BQ tP tQ
      htQ hearlyQ hgt hEorder hOld hEP hFQ hBQ hBQlower
      hEold hFold hQfirst hBQtie hPoldTop hPfirst)

/-- It suffices that at least one first slope occurs before the grade
direction: whichever slope is strictly earlier then also lies before
that direction. -/
theorem ramified_exact_pair_first_slopes_equal_of_one_early
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F BP BQ : ℤ × ℕ) (tP tQ : ℚ)
    (htP : 0 < tP) (htQ : 0 < tQ)
    (hearly : tP < (l : ℚ) * ((ρ+σ : ℤ) : ℚ) ∨
      tQ < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hEorder : 2 ≤ E.2) (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : BP ∈ ramifiedPBWSupport l hl P)
    (hBQ : BQ ∈ ramifiedPBWSupport l hl Q)
    (hBPlower : BP.2 < E.2) (hBQlower : BQ.2 < F.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hPoldTop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP)
    (hQoldTop : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q ≤ VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ))
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hBPtie : ((ramifiedWeight l ρ σ BP : ℤ) : ℚ) - tP * (BP.2 : ℚ) =
      (VP : ℚ) - tP * (E.2 : ℚ))
    (hBQtie : ((ramifiedWeight l ρ σ BQ : ℤ) : ℚ) - tQ * (BQ.2 : ℚ) =
      (VQ : ℚ) - tQ * (F.2 : ℚ)) :
    tP = tQ := by
  rcases lt_trichotomy tP tQ with hlt | heq | hgt
  · have hearlyP : tP < (l : ℚ) * ((ρ+σ : ℤ) : ℚ) := by
      rcases hearly with h | h
      · exact h
      · exact hlt.trans h
    exact False.elim (ramified_exact_pair_no_earlier_first_slope
      l hl ρ σ hρ P Q hcomm VP VQ E F BP tP tQ
      htP hearlyP hlt hForder hOld hEP hFQ hBP hBPlower
      hEold hFold hPfirst hBPtie hQoldTop hQfirst)
  · exact heq
  · have hearlyQ : tQ < (l : ℚ) * ((ρ+σ : ℤ) : ℚ) := by
      rcases hearly with h | h
      · exact hgt.trans h
      · exact h
    exact False.elim (ramified_exact_pair_no_later_first_slope
      l hl ρ σ hρ P Q hcomm VP VQ E F BQ tP tQ
      htQ hearlyQ hgt hEorder hOld hEP hFQ hBQ hBQlower
      hEold hFold hQfirst hBQtie hPoldTop hPfirst)

end Dixmier.Weyl
