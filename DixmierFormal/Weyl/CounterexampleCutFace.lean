/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCompanionJosephFrontier
public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Maximum-root cut of a polynomial counterexample

The internally proved companion supplies the selected negative grade.
The cut reaches a common primitive direction with positive weights and
the unchanged reduced ratio, without a separate companion assumption.
The ramified forbidden-corner exclusion is not asserted here.
-/

namespace Dixmier.Weyl

set_option maxHeartbeats 800000

open MvPolynomial Polynomial

/-- A negative-grade atom on the old face makes its degree endpoint
negative after scaling to any admissible coefficient index. -/
theorem negative_face_cut_degree_and_end
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ)) (hsum : 0 < ρ + σ)
    (hneg : ∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) :
    0 < (cutPoly ρ σ P.1).natDegree ∧
      (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
        (ramifiedCutExponent l ρ σ + (l : ℤ)) *
          ((cutPoly ρ σ P.1).natDegree : ℤ) < 0 := by
  obtain ⟨e, he, hg⟩ := hneg
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective e
  have hw := (polynomialFace_point_source_data P ρ σ i j he).2
  have hc : (cutPoly ρ σ P.1).coeff j ≠ 0 := by
    rw [cutPoly_coeff_at_face_point P ρ σ i j hρ hw]
    exact MvPolynomial.mem_support_iff.mp he
  have hjD := Polynomial.le_natDegree_of_ne_zero hc
  have hjDz : (j : ℤ) ≤ (cutPoly ρ σ P.1).natDegree := by
    exact_mod_cast hjD
  simp [grade, expo] at hg
  have hDpos : 0 < (cutPoly ρ σ P.1).natDegree := by omega
  have hbase : vDeg ρ σ P.1 - (ρ + σ) *
      ((cutPoly ρ σ P.1).natDegree : ℤ) < 0 := by
    nlinarith [mul_pos hρ (show 0 < (j : ℤ) - i by omega),
      mul_nonneg (le_of_lt hsum) (sub_nonneg.mpr hjDz)]
  have hlz : (0 : ℤ) < l := by exact_mod_cast hl
  have hscaled := mul_neg_of_pos_of_neg hlz hbase
  have hid : ρ * ((((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        ((cutPoly ρ σ P.1).natDegree : ℤ)) =
      (l : ℤ) * (vDeg ρ σ P.1 - (ρ + σ) *
        ((cutPoly ρ σ P.1).natDegree : ℤ)) := by
    unfold ramifiedCutExponent
    calc
      _ = (ρ * ((l : ℤ) / ρ)) * vDeg ρ σ P.1 -
          ((ρ * ((l : ℤ) / ρ)) * σ + ρ * (l : ℤ)) *
            ((cutPoly ρ σ P.1).natDegree : ℤ) := by ring
      _ = _ := by rw [Int.mul_ediv_cancel' hdiv]; ring
  refine ⟨hDpos, ?_⟩
  rw [← hid] at hscaled
  nlinarith

theorem counterexample_maxRoot_cut_positive_ratio
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hneg : ∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) :
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
      let G : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
          ramifiedCutExponent l ρ σ*(N : ℤ),N)
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s U ∧
      ramifiedWeight l r s G = ramifiedWeightDeg l hl r s V ∧
      0 < ramifiedWeightDeg l hl r s U ∧
      0 < ramifiedWeightDeg l hl r s V ∧
      ramifiedWeightDeg l hl r s V * (d : ℤ) =
        ramifiedWeightDeg l hl r s U * (n : ℤ) ∧
      E.1 - (l : ℤ)*(E.2 : ℤ) < 0 ∧
      G.1 - (l : ℤ)*(G.2 : ℤ) < 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        ramifiedWeight l r s p = ramifiedWeightDeg l hl r s U →
          E.1 - (l : ℤ)*(E.2 : ℤ) ≤ p.1 - (l : ℤ)*(p.2 : ℤ)) ∧
      (∀ q ∈ ramifiedPBWSupport l hl V,
        ramifiedWeight l r s q = ramifiedWeightDeg l hl r s V →
          G.1 - (l : ℤ)*(G.2 : ℤ) ≤ q.1 - (l : ℤ)*(q.2 : ℤ)) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
        ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s U) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
        ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s V) := by
  obtain ⟨hcutDegree, hOldEnd⟩ :=
    negative_face_cut_degree_and_end l hl P ρ σ hρ hdiv hdir.2 hneg
  have hP := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQ := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hQP := hpair.1
  have hgrade := preliminary_companion_maxRoot_cut_grade_negative
    ggv_preliminary_companion_proved l hl P Q hpair ρ σ hdir hρ hdiv
      hdirP hcutDegree hOldEnd
  obtain ⟨c,r,s,hrootP,hmP,hdirNew,hr,hsneg,hEtop,hFtop,hEmin,hFmin,hBP,hBQ⟩ :=
    exactPair_maxRoot_cut_exists_primitive_common_face
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ
      hQP hsum d n hd hn hweight hcop hgrade
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
    nlinarith [hgrade]
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
    hnew.1,hnew.2.1,hnew.2.2,hEgrade,hFgrade,hEmin,hFmin,hBP,hBQ⟩


/-- The selected cut endpoint is minimal in grade on the new face. -/
theorem counterexample_maxRoot_cut_min_grade_face
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hneg : ∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) :
    ∃ c : ℂ, ∃ r s : ℤ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      IsDirection r s ∧ 0 < r ∧ (σ ≤ 0 → s < 0) ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let k := ramifiedCutExponent l ρ σ
      let M := (cutPoly ρ σ P.1).rootMultiplicity c
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      let E : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ P.1 - k*(M : ℤ),M)
      let F : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ Q.1 - k*(N : ℤ),N)
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s U ∧
      ramifiedWeight l r s F = ramifiedWeightDeg l hl r s V ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        ramifiedWeight l r s p = ramifiedWeightDeg l hl r s U →
          E.1 - (l : ℤ)*(E.2 : ℤ) ≤
            p.1 - (l : ℤ)*(p.2 : ℤ)) ∧
      (∀ q ∈ ramifiedPBWSupport l hl V,
        ramifiedWeight l r s q = ramifiedWeightDeg l hl r s V →
          F.1 - (l : ℤ)*(F.2 : ℤ) ≤
            q.1 - (l : ℤ)*(q.2 : ℤ)) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
        ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s U) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
        ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s V) := by
  obtain ⟨hcutDegree, hOldEnd⟩ :=
    negative_face_cut_degree_and_end l hl P ρ σ hρ hdiv hdir.2 hneg
  have hP := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQ := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hQP := hpair.1
  have hgrade := preliminary_companion_maxRoot_cut_grade_negative
    ggv_preliminary_companion_proved l hl P Q hpair ρ σ hdir hρ hdiv
      hdirP hcutDegree hOldEnd
  exact exactPair_maxRoot_cut_exists_primitive_common_face
    l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP
      hsum d n hd hn hweight hcop hgrade

end Dixmier.Weyl
