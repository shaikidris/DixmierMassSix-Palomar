/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutSourceEndpoints
public import DixmierFormal.Weyl.RamifiedGradeExactPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A common first adjacent face from exact pair data

An exact pair with parallel negative-grade old starts and both start
orders at least two has one early first face. The one-sided support
lemmas force a lower-order point on the other member; finite support
then constructs its first face. The two first slopes coincide.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_exists_common_early_adjacent_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F : ℤ × ℕ)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hEweight : ramifiedWeight l ρ σ E = VP)
    (hFweight : ramifiedWeight l ρ σ F = VQ)
    (hEgrade : E.1 - (l : ℤ) * (E.2 : ℤ) < 0)
    (hFgrade : F.1 - (l : ℤ) * (F.2 : ℤ) < 0)
    (hEorder : 2 ≤ E.2) (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hPtop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP)
    (hQtop : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q ≤ VQ)
    (hPstart : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = VP → E.2 ≤ p.2)
    (hQstart : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q = VQ → F.2 ≤ q.2) :
    ∃ t : ℚ, 0 < t ∧
      t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl P,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (VP : ℚ) - t * (E.2 : ℚ)) ∧
      (∀ q ∈ ramifiedPBWSupport l hl Q,
        (ramifiedWeight l ρ σ q : ℚ) - t * (q.2 : ℚ) ≤
          (VQ : ℚ) - t * (F.2 : ℚ)) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl P, BP.2 < E.2 ∧
        (ramifiedWeight l ρ σ BP : ℚ) - t * (BP.2 : ℚ) =
          (VP : ℚ) - t * (E.2 : ℚ)) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl Q, BQ.2 < F.2 ∧
        (ramifiedWeight l ρ σ BQ : ℚ) - t * (BQ.2 : ℚ) =
          (VQ : ℚ) - t * (F.2 : ℚ)) := by
  have hfirst := ramified_exact_pair_exists_early_adjacent_slope
    l hl ρ σ hρ hsum P Q hcomm VP VQ E F
    hEweight hFweight hEgrade hFgrade
    hPtop hQtop hPstart hQstart
  rcases hfirst with ⟨tP,htP,hearlyP,hPfirst,⟨BP,hBP,hBPlower,hBPtie⟩⟩ |
    ⟨tQ,htQ,hearlyQ,hQfirst,⟨BQ,hBQ,hBQlower,hBQtie⟩⟩
  · obtain ⟨BQ₀,hBQ₀,hBQ₀lower⟩ :=
      ramified_exact_pair_first_slope_forces_mate_lower_order
        l hl ρ σ hρ P Q hcomm VP VQ E F BP tP
        htP hearlyP hForder hOld hEP hFQ hBP hBPlower
        hEweight hFweight hPfirst hBPtie hQtop
    obtain ⟨tQ,htQ,hQfirst,⟨BQ,hBQ,hBQlower,hBQtie⟩⟩ :=
      finiteSupport_exists_adjacent_rational_slope
        (ramifiedPBWSupport l hl Q) (ramifiedWeight l ρ σ)
        VQ F.2 hQtop hQstart ⟨BQ₀,hBQ₀,hBQ₀lower⟩
    have heq := ramified_exact_pair_first_slopes_equal_of_one_early
      l hl ρ σ hρ P Q hcomm VP VQ E F BP BQ tP tQ
      htP htQ (Or.inl hearlyP) hEorder hForder hOld
      hEP hFQ hBP hBQ hBPlower hBQlower
      hEweight hFweight hPtop hQtop hPfirst hQfirst
      hBPtie hBQtie
    rw [← heq] at hQfirst hBQtie
    exact ⟨tP,htP,hearlyP,hPfirst,hQfirst,
      ⟨BP,hBP,hBPlower,hBPtie⟩,
      ⟨BQ,hBQ,hBQlower,hBQtie⟩⟩
  · obtain ⟨BP₀,hBP₀,hBP₀lower⟩ :=
      ramified_exact_pair_mate_first_slope_forces_lower_order
        l hl ρ σ hρ P Q hcomm VP VQ E F BQ tQ
        htQ hearlyQ hEorder hOld hEP hFQ hBQ hBQlower
        hEweight hFweight hQfirst hBQtie hPtop
    obtain ⟨tP,htP,hPfirst,⟨BP,hBP,hBPlower,hBPtie⟩⟩ :=
      finiteSupport_exists_adjacent_rational_slope
        (ramifiedPBWSupport l hl P) (ramifiedWeight l ρ σ)
        VP E.2 hPtop hPstart ⟨BP₀,hBP₀,hBP₀lower⟩
    have heq := ramified_exact_pair_first_slopes_equal_of_one_early
      l hl ρ σ hρ P Q hcomm VP VQ E F BP BQ tP tQ
      htP htQ (Or.inr hearlyQ) hEorder hForder hOld
      hEP hFQ hBP hBQ hBPlower hBQlower
      hEweight hFweight hPtop hQtop hPfirst hQfirst
      hBPtie hBQtie
    rw [heq] at hPfirst hBPtie
    exact ⟨tQ,htQ,hearlyQ,hPfirst,hQfirst,
      ⟨BP,hBP,hBPlower,hBPtie⟩,
      ⟨BQ,hBQ,hBQlower,hBQtie⟩⟩

end Dixmier.Weyl
