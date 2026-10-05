/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NegativeCrossing
public import DixmierFormal.Weyl.HorizontalCrossing
public import DixmierFormal.Weyl.TwoRootTotalDegree
public import DixmierFormal.Weyl.Fourier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Complex mass-six generation relative to the published GGV inputs

The case split is applied to the original operator or its Fourier image. The
crossing alternatives use the two proved exclusions, while the remaining
total-degree alternative uses the sparse two-root contradiction. No restriction
is placed on the mate's mass or degree.
-/

namespace Dixmier.Weyl

private theorem caseAlternative_contradiction (H : GGVInputs) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q) (hmass : mass P.1 ≤ 6)
    (halt : CaseAlternative P.1) : False := by
  rcases halt with hcross | hlarge | htwo
  · obtain ⟨ρ, σ, hρ, hσlo, hσhi, hgcd, hc⟩ := hcross
    by_cases hzero : σ = 0
    · subst σ
      have hρone : ρ = 1 := by
        have hh : ρ.natAbs = 1 := by
          simpa only [Int.gcd_def, Int.natAbs_zero, Nat.gcd_zero_right] using hgcd
        omega
      subst ρ
      exact (horizontalCrossingExclusion_of_GGV H P Q hpair hmass) hc
    · let r : ℕ := ρ.toNat
      let s : ℕ := (-σ).toNat
      have hr : (r : ℤ) = ρ := by dsimp [r]; omega
      have hs : (s : ℤ) = -σ := by dsimp [s]; omega
      have hspos : 1 ≤ s := by omega
      have hsr : s < r := by omega
      have hcop : Nat.Coprime r s := by
        have hσ : σ = -(s : ℤ) := by omega
        simpa only [Int.gcd_def, ← hr, hσ, Int.natAbs_natCast, Int.natAbs_neg,
          Nat.Coprime] using hgcd
      have hc' : IsStrictCrossing (r : ℤ) (-(s : ℤ)) P.1 := by
        simpa [hr, hs] using hc
      exact (negativeCrossingExclusion_of_GGV H P Q hpair hmass r s hspos hsr hcop) hc'
  · omega
  · exact twoRoot_massSix_contradiction_of_GGV H P Q hpair hmass htwo

/-- The paper's generation theorem over `ℂ`, conditional on the six explicit published
GGV inputs. The mate is unrestricted. -/
theorem massSixGeneration_complex_of_GGV (H : GGVInputs) :
    ∀ P Q : A1 ℂ, Q * P - P * Q = 1 → mass P.1 ≤ 6 →
      Algebra.adjoin ℂ {P, Q} = ⊤ := by
  intro P Q hcomm hmass
  by_contra hgen
  have hpair : IsCounterexamplePair P Q := ⟨hcomm, hgen⟩
  rcases H.caseSplit P Q hpair with hP | hF
  · exact caseAlternative_contradiction H P Q hpair hmass hP
  · let PF : A1 ℂ := fourierAlgHom ℂ P
    let QF : A1 ℂ := fourierAlgHom ℂ Q
    have hpairF : IsCounterexamplePair PF QF := isCounterexamplePair_fourier P Q hpair
    have hmassF : mass PF.1 ≤ 6 := by
      have hh := mass_fourier_A1 P
      rw [fourier_eq_algHom] at hh
      exact hh.le.trans hmass
    have hF' : CaseAlternative PF.1 := by
      simpa [PF, fourier_eq_algHom] using hF
    exact caseAlternative_contradiction H PF QF hpairF hmassF hF'

end Dixmier.Weyl
