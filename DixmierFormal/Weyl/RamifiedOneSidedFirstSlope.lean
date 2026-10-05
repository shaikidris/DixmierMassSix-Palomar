/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCommonFirstSlope

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# One-sided first slope forces lower-order support on the mate

If one member has a first adjacent face and the other has no support
below its old endpoint, the latter remains a singleton at every positive
tilt. The exact relation excludes this configuration under the endpoint
and root-order hypotheses.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_first_slope_forces_mate_lower_order
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F BP : ℤ × ℕ) (tP : ℚ)
    (htP : 0 < tP)
    (hearly : tP < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : BP ∈ ramifiedPBWSupport l hl P)
    (hBPlower : BP.2 < E.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ))
    (hBPtie : ((ramifiedWeight l ρ σ BP : ℤ) : ℚ) - tP * (BP.2 : ℚ) =
      (VP : ℚ) - tP * (E.2 : ℚ))
    (hQoldTop : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q ≤ VQ) :
    ∃ BQ ∈ ramifiedPBWSupport l hl Q, BQ.2 < F.2 := by
  by_contra hnone
  have hQorder : ∀ q ∈ ramifiedPBWSupport l hl Q, F.2 ≤ q.2 := by
    intro q hq
    by_contra hlt
    exact hnone ⟨q,hq,Nat.lt_of_not_ge hlt⟩
  let tQ : ℚ := tP + 1
  have hlt : tP < tQ := by dsimp [tQ]; linarith
  have hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ) := by
    intro q hq
    have hw : ((ramifiedWeight l ρ σ q : ℤ) : ℚ) ≤ (VQ : ℚ) :=
      by exact_mod_cast hQoldTop q hq
    have hn : (F.2 : ℚ) ≤ (q.2 : ℚ) := by
      exact_mod_cast hQorder q hq
    have htQ : 0 ≤ tQ := by dsimp [tQ]; linarith
    nlinarith [mul_nonneg htQ (sub_nonneg.mpr hn)]
  exact False.elim (ramified_exact_pair_no_earlier_first_slope
    l hl ρ σ hρ P Q hcomm VP VQ E F BP tP tQ
    htP hearly hlt hForder hOld hEP hFQ hBP hBPlower
    hEold hFold hPfirst hBPtie hQoldTop hQfirst)

/-- The same forced lower-order support when Q supplies the initial
first-slope witness. The exact pair is reversed using Q and -P. -/
theorem ramified_exact_pair_mate_first_slope_forces_lower_order
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F BQ : ℤ × ℕ) (tQ : ℚ)
    (htQ : 0 < tQ)
    (hearly : tQ < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hEorder : 2 ≤ E.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBQ : BQ ∈ ramifiedPBWSupport l hl Q)
    (hBQlower : BQ.2 < F.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hBQtie : ((ramifiedWeight l ρ σ BQ : ℤ) : ℚ) - tQ * (BQ.2 : ℚ) =
      (VQ : ℚ) - tQ * (F.2 : ℚ))
    (hPoldTop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP) :
    ∃ BP ∈ ramifiedPBWSupport l hl P, BP.2 < E.2 := by
  by_contra hnone
  have hPorder : ∀ p ∈ ramifiedPBWSupport l hl P, E.2 ≤ p.2 := by
    intro p hp
    by_contra hlt
    exact hnone ⟨p,hp,Nat.lt_of_not_ge hlt⟩
  let tP : ℚ := tQ + 1
  have hlt : tQ < tP := by dsimp [tP]; linarith
  have hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ) := by
    intro p hp
    have hw : ((ramifiedWeight l ρ σ p : ℤ) : ℚ) ≤ (VP : ℚ) :=
      by exact_mod_cast hPoldTop p hp
    have hn : (E.2 : ℚ) ≤ (p.2 : ℚ) := by
      exact_mod_cast hPorder p hp
    have htP : 0 ≤ tP := by dsimp [tP]; linarith
    nlinarith [mul_nonneg htP (sub_nonneg.mpr hn)]
  exact False.elim (ramified_exact_pair_no_later_first_slope
    l hl ρ σ hρ P Q hcomm VP VQ E F BQ tP tQ
    htQ hearly hlt hEorder hOld hEP hFQ hBQ hBQlower
    hEold hFold hQfirst hBQtie hPoldTop hPfirst)

end Dixmier.Weyl
