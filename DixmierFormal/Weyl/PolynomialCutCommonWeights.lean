/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutCommonDirection
public import DixmierFormal.Weyl.RamifiedCommonFaceRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positive weights and ratio after the polynomial maximum-root cut

The common primitive cut direction supplied by the exact pair also
preserves the reduced weight ratio. This combines the selected-root
order identity with positivity of parallel exact-pair top weights.
-/

namespace Dixmier.Weyl

set_option maxHeartbeats 800000

theorem exactPair_maxRoot_cut_exists_common_face_positive_ratio
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hPgrade : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0) :
    ∃ c : ℂ, ∃ r s : ℤ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      IsDirection r s ∧ 0 < r ∧ (σ ≤ 0 → s < 0) ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let M := (cutPoly ρ σ P.1).rootMultiplicity c
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      let E : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
          ramifiedCutExponent l ρ σ*(M : ℤ),M)
      let F : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
          ramifiedCutExponent l ρ σ*(N : ℤ),N)
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s U ∧
      ramifiedWeight l r s F = ramifiedWeightDeg l hl r s V ∧
      0 < ramifiedWeightDeg l hl r s U ∧
      0 < ramifiedWeightDeg l hl r s V ∧
      ramifiedWeightDeg l hl r s V * (d : ℤ) =
        ramifiedWeightDeg l hl r s U * (n : ℤ) ∧
      E.1 - (l : ℤ)*(E.2 : ℤ) < 0 ∧
      F.1 - (l : ℤ)*(F.2 : ℤ) < 0 ∧
      (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
        ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s U) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
        ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s V) := by
  obtain ⟨c,r,s,hrootP,hmP,hdirNew,hr,hsneg,hEtop,hFtop,_,_,hBP,hBQ⟩ :=
    exactPair_maxRoot_cut_exists_primitive_common_face
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ
      hQP hsum d n hd hn hweight hcop hPgrade
  let M := (cutPoly ρ σ P.1).rootMultiplicity c
  let N := (cutPoly ρ σ Q.1).rootMultiplicity c
  let E : ℤ × ℕ :=
    (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
      ramifiedCutExponent l ρ σ*(M : ℤ),M)
  let F : ℤ × ℕ :=
    (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
      ramifiedCutExponent l ρ σ*(N : ℤ),N)
  have hMpos : 0 < M := by
    have hpne := cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
    exact (Polynomial.rootMultiplicity_pos hpne).mpr hrootP
  obtain ⟨_,hrootNat⟩ := exactPair_cutPoly_common_root_and_multiplicity
    P Q ρ σ hdir hρ hP hQ hdirP hdirQ hQP hsum c hrootP
  have hrootZ : vDeg ρ σ Q.1 * (M : ℤ) =
      vDeg ρ σ P.1 * (N : ℤ) := by
    have h := congrArg (fun a : ℕ => (a : ℤ)) hrootNat
    push_cast at h
    simpa [M,N,Int.toNat_of_nonneg (le_of_lt hP),
      Int.toNat_of_nonneg (le_of_lt hQ)] using h
  have hparallel : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1 := by
    dsimp [E,F]
    nlinarith [congrArg (fun z : ℤ => ((l : ℤ) / ρ)*z) hrootZ]
  have horder : (E.2 : ℤ)*(n : ℤ) = (F.2 : ℤ)*(d : ℤ) := by
    have ha := congrArg (fun z : ℤ => z*(M : ℤ)) hweight
    have hb := congrArg (fun z : ℤ => z*(d : ℤ)) hrootZ
    have hfactor : vDeg ρ σ P.1 * ((n : ℤ)*(M : ℤ)) =
        vDeg ρ σ P.1 * ((d : ℤ)*(N : ℤ)) := by
      nlinarith [ha,hb]
    have hcross : (n : ℤ)*(M : ℤ) = (d : ℤ)*(N : ℤ) :=
      mul_left_cancel₀ (ne_of_gt hP) hfactor
    simpa [E,F, mul_comm] using hcross
  have hEgrade : E.1 - (l : ℤ)*(E.2 : ℤ) < 0 := by
    dsimp [E,M]
    rw [hmP]
    nlinarith [hPgrade]
  have hNpos : (0 : ℤ) < F.2 := by
    have hMZ : (0 : ℤ) < E.2 := by exact_mod_cast hMpos
    have hnZ : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
    have hprod : 0 < (E.2 : ℤ)*(n : ℤ) := mul_pos hMZ hnZ
    have hNnon : (0 : ℤ) ≤ F.2 := by exact_mod_cast Nat.zero_le F.2
    have hdZ : (0 : ℤ) ≤ d := by exact_mod_cast Nat.zero_le d
    by_contra hbad
    have hzero : (F.2 : ℤ) = 0 := by omega
    rw [hzero] at horder
    nlinarith [horder,hprod]
  have hFgrade : F.1 - (l : ℤ)*(F.2 : ℤ) < 0 := by
    have hscale : (E.2 : ℤ)*(F.1 - (l : ℤ)*(F.2 : ℤ)) =
        (F.2 : ℤ)*(E.1 - (l : ℤ)*(E.2 : ℤ)) := by
      nlinarith [hparallel]
    have hMZ : (0 : ℤ) < E.2 := by exact_mod_cast hMpos
    have hneg := mul_neg_of_pos_of_neg hNpos hEgrade
    by_contra hbad
    have hnonneg : 0 ≤ F.1 - (l : ℤ)*(F.2 : ℤ) := le_of_not_gt hbad
    have hprod := mul_nonneg (le_of_lt hMZ) hnonneg
    nlinarith [hscale,hneg,hprod]
  have hexact :
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 :=
    ramifiedCutAut_exact_pair l hl ρ σ c _ _
      (polynomialRamifiedLift_bracket_one l hl P Q hQP)
  have hnew := ramified_exact_pair_parallel_top_weights_positive_ratio
    l hl r s hr hdirNew.2
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
    hexact E F (by simpa [E] using hMpos) hparallel
    (by simpa [E,F,M,N] using hEtop)
    (by simpa [E,F,M,N] using hFtop)
    d n (by omega) (by omega) horder
  exact ⟨c,r,s,hrootP,hmP,hdirNew,hr,hsneg,hEtop,hFtop,
    hnew.1,hnew.2.1,hnew.2.2,hEgrade,hFgrade,hBP,hBQ⟩

end Dixmier.Weyl
