/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutMaxRootExactPair
public import DixmierFormal.Weyl.PolynomialRamifiedCutEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The exact cut-pair start criterion from a polynomial source direction

The genuine polynomial face, exact Weyl relation, and faithful finite
ramified lift supply the hypotheses of the maximum-root pair theorem.
-/

namespace Dixmier.Weyl

theorem polynomialCut_exact_pair_maxRoot_start_criterion
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ+σ)
    (hcomm : Q*P-P*Q = 1)
    (hdir : InDir ρ σ P.1) :
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
      (((m : ℂ) * ((ramifiedPBWTopLaurent l hl Q' M : ℤ) : ℂ) -
        (M : ℂ) * ((r-k*(m : ℤ) : ℤ) : ℂ) ≠ 0) ↔
          m+M = 1 ∧
            r-k*(m : ℤ)+ramifiedPBWTopLaurent l hl Q' M = (l : ℤ)) := by
  dsimp only
  let r : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ P.1
  obtain ⟨d₁,d₂,hd₁,hd₂,hne⟩ :=
    Finset.one_lt_card_iff.mp hdir
  obtain ⟨⟨i₁,j₁⟩,rfl⟩ := expo_surjective d₁
  obtain ⟨⟨i₂,j₂⟩,rfl⟩ := expo_surjective d₂
  obtain ⟨hs₁,hw₁⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i₁ j₁ hd₁
  obtain ⟨hs₂,hw₂⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i₂ j₂ hd₂
  have hdistinct :
      (((l : ℤ) * (i₁ : ℤ)),j₁) ≠
        (((l : ℤ) * (i₂ : ℤ)),j₂) := by
    intro he
    have hi : (l : ℤ) * (i₁ : ℤ) =
        (l : ℤ) * (i₂ : ℤ) := (Prod.mk.inj he).1
    have hj : j₁ = j₂ := (Prod.mk.inj he).2
    have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
    have hii : i₁ = i₂ := by
      have he' : (i₁ : ℤ) = (i₂ : ℤ) := (mul_left_cancel₀ hlz) hi
      exact_mod_cast he'
    exact hne (congrArg (fun p : ℕ × ℕ => expo p.1 p.2)
      (Prod.ext hii hj))
  have hbound : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r := by
    intro u n hm
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hm
  have hpair := ramifiedCutAut_maxRoot_exact_pair_start_criterion
    l hl ρ σ r ((l : ℤ)*(i₁ : ℤ)) ((l : ℤ)*(i₂ : ℤ))
    j₁ j₂ hρ hdiv hpos
    (polynomialRamifiedLift l P) (polynomialRamifiedLift l Q)
    (polynomialRamifiedLift_bracket_one l hl P Q hcomm)
    hs₁ hs₂ hw₁ hw₂ hdistinct hbound
  simpa only [r, polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv,
    polynomialRamifiedFace_maxRootMult_eq_cutPoly l hl P ρ σ hρ hdiv]
    using hpair

end Dixmier.Weyl
