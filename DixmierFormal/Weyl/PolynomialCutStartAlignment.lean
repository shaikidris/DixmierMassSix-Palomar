/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutExactStartPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Parallel old-face starts after a repeated-root cut

A selected root of multiplicity at least two prevents the unique
constant first-contraction output. The exact Weyl equation then forces
the two sheared old-face start endpoints to have zero determinant.
-/

namespace Dixmier.Weyl

theorem polynomialCut_repeated_root_start_alignment
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ)
    (hcomm : Q*P-P*Q = 1)
    (hdir : InDir ρ σ P.1)
    (hlarge : 2 ≤ maxRootMult (cutPoly ρ σ P.1)) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    ∃ (c : ℂ) (M : ℕ),
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      let Q' := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let k := ramifiedCutExponent l ρ σ
      let m := Polynomial.rootMultiplicity c (cutPoly ρ σ P.1)
      M ∈ (ramifiedPBWCoeffs l hl Q').support ∧
      ramifiedWeight l ρ σ
        (ramifiedPBWTopLaurent l hl Q' M,M) =
          ramifiedWeightDeg l hl ρ σ Q' ∧
      (∀ b ∈ (ramifiedPBWCoeffs l hl Q').support,
        ramifiedWeight l ρ σ
          (ramifiedPBWTopLaurent l hl Q' b,b) =
            ramifiedWeightDeg l hl ρ σ Q' → M ≤ b) ∧
      (m : ℂ) * ((ramifiedPBWTopLaurent l hl Q' M : ℤ) : ℂ) -
        (M : ℂ) * ((r-k*(m : ℤ) : ℤ) : ℂ) = 0 := by
  dsimp only
  obtain ⟨c,M,hroot,hm,hM,hQtop,hQmin,hcriterion⟩ :=
    polynomialCut_exact_pair_maxRoot_start_criterion
      l hl P Q ρ σ hρ hdiv hpos hcomm hdir
  have hm2 : 2 ≤ Polynomial.rootMultiplicity c (cutPoly ρ σ P.1) := by
    rw [hm]
    exact hlarge
  have hdet :
      (Polynomial.rootMultiplicity c (cutPoly ρ σ P.1) : ℂ) *
        ((ramifiedPBWTopLaurent l hl
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) M : ℤ) : ℂ) -
        (M : ℂ) *
          ((((l : ℤ) / ρ) * vDeg ρ σ P.1 -
            ramifiedCutExponent l ρ σ *
              (Polynomial.rootMultiplicity c (cutPoly ρ σ P.1) : ℤ) : ℤ) : ℂ) = 0 := by
    by_contra hne
    obtain ⟨horder,_⟩ := hcriterion.mp hne
    omega
  exact ⟨c,M,hroot,hm,hM,hQtop,hQmin,hdet⟩

end Dixmier.Weyl
