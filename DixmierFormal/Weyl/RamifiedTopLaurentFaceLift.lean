/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A face point lifts to the canonical top Laurent point at its order

When a PBW point is on the maximum Newton face and the horizontal
weight coefficient is positive, its derivative-order coefficient has
the same canonical top Laurent exponent. Thus a lower-order face
point supplies the exact canonical witness used in endpoint theorems.
-/

namespace Dixmier.Weyl

theorem ramified_face_point_topLaurent_at_order
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l) (B : ℤ × ℕ)
    (hB : B ∈ ramifiedPBWSupport l hl T)
    (hBtop : ramifiedWeight l ρ σ B =
      ramifiedWeightDeg l hl ρ σ T)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ T) :
    B.2 ∈ (ramifiedPBWCoeffs l hl T).support ∧
      ramifiedPBWTopLaurent l hl T B.2 = B.1 ∧
      ramifiedWeight l ρ σ
        (ramifiedPBWTopLaurent l hl T B.2,B.2) =
          ramifiedWeightDeg l hl ρ σ T := by
  have hBne : ((ramifiedPBWCoeffs l hl T) B.2).coeff B.1 ≠ 0 :=
    (ramifiedPBWSupport_mem_iff l hl T B.1 B.2).mp hB
  have hn : B.2 ∈ (ramifiedPBWCoeffs l hl T).support := by
    apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz] at hBne
  have hle : B.1 ≤ ramifiedPBWTopLaurent l hl T B.2 :=
    ramifiedPBWTopLaurent_upper l hl T B.2 B.1
      (Finsupp.mem_support_iff.mpr hBne)
  have hTopMem := ramifiedPBWTopLaurent_support l hl T B.2 hn
  have hTopLe := hupper _ hTopMem
  have heq : ramifiedPBWTopLaurent l hl T B.2 = B.1 := by
    dsimp [ramifiedWeight] at hBtop hTopLe
    nlinarith
  exact ⟨hn,heq,by simpa [heq] using hBtop⟩

end Dixmier.Weyl
