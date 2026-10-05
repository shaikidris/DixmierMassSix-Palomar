/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCommonAdjacentDirection
public import DixmierFormal.Weyl.RamifiedCommonIntegralFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A common adjacent direction from the polynomial maximum-root cut

The polynomial source, reduced nonintegral weight ratio, and selected
negative-grade condition supply all old-face hypotheses of the exact
ramified common-face theorem at the same maximum root.
-/

namespace Dixmier.Weyl

theorem exactPair_maxRoot_cut_exists_common_early_adjacent_face
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
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let rP := ((l : ℤ) / ρ) * vDeg ρ σ P.1
      let rQ := ((l : ℤ) / ρ) * vDeg ρ σ Q.1
      let M := (cutPoly ρ σ P.1).rootMultiplicity c
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      ∃ t : ℚ, 0 < t ∧
        t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
        (∀ p ∈ ramifiedPBWSupport l hl U,
          (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
            ((ρ*rP : ℤ) : ℚ) - t * (M : ℚ)) ∧
        (∀ q ∈ ramifiedPBWSupport l hl V,
          (ramifiedWeight l ρ σ q : ℚ) - t * (q.2 : ℚ) ≤
            ((ρ*rQ : ℤ) : ℚ) - t * (N : ℚ)) ∧
        (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < M ∧
          (ramifiedWeight l ρ σ BP : ℚ) - t * (BP.2 : ℚ) =
            ((ρ*rP : ℤ) : ℚ) - t * (M : ℚ)) ∧
        (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
          (ramifiedWeight l ρ σ BQ : ℚ) - t * (BQ.2 : ℚ) =
            ((ρ*rQ : ℤ) : ℚ) - t * (N : ℚ)) := by
  have hpos : 0 < ρ + σ := hdir.2
  obtain ⟨c,M,N,hrootP,hmP,hMroot,hN,hm2,hn2,hpointP,hpointQ,hOld,hexact⟩ :=
    exactPair_maxRoot_cut_parallel_endpoints_and_orders
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
      d n hd hn hweight hcop
  let rP : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ P.1
  let rQ : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ Q.1
  let k : ℤ := ramifiedCutExponent l ρ σ
  let E : ℤ × ℕ := (rP-k*(M : ℤ),M)
  let F : ℤ × ℕ := (rQ-k*(N : ℤ),N)
  have hEgrade : E.1 - (l : ℤ) * (E.2 : ℤ) < 0 := by
    dsimp [E,rP,k]
    rw [hmP]
    nlinarith [hPgrade]
  have hFgrade : F.1 - (l : ℤ) * (F.2 : ℤ) < 0 := by
    have hscale : (M : ℤ) * (F.1 - (l : ℤ)*(N : ℤ)) =
        (N : ℤ) * (E.1 - (l : ℤ)*(M : ℤ)) := by
      calc
        (M : ℤ) * (F.1 - (l : ℤ)*(N : ℤ)) =
            (M : ℤ)*F.1 - (l : ℤ)*(M : ℤ)*(N : ℤ) := by ring
        _ = (N : ℤ)*E.1 - (l : ℤ)*(M : ℤ)*(N : ℤ) := by
          rw [show (M : ℤ)*F.1 = (N : ℤ)*E.1 from hOld]
        _ = (N : ℤ) * (E.1 - (l : ℤ)*(M : ℤ)) := by ring
    have hNpos : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
    have hMpos : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
    have hneg := mul_neg_of_pos_of_neg hNpos hEgrade
    by_contra hbad
    have hnonneg : 0 ≤ F.1 - (l : ℤ)*(N : ℤ) := le_of_not_gt hbad
    have hprod := mul_nonneg (le_of_lt hMpos) hnonneg
    nlinarith [hscale,hneg,hprod]
  obtain ⟨aP,bP,haP,_,_⟩ := Finset.one_lt_card_iff.mp hdirP
  obtain ⟨⟨iP,jP⟩,rfl⟩ := expo_surjective aP
  obtain ⟨aQ,bQ,haQ,_,_⟩ := Finset.one_lt_card_iff.mp hdirQ
  obtain ⟨⟨iQ,jQ⟩,rfl⟩ := expo_surjective aQ
  have hsP := polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hpos iP jP haP c
  have hsQ := polynomialRamifiedCut_root_start_on_old_face
    l hl Q ρ σ hρ hdiv hpos iQ jQ haQ c
  have hsourceP : ∀ u : ℤ, ∀ a : ℕ,
      (u,a) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
      ramifiedWeight l ρ σ (u,a) ≤ ρ*rP := by
    intro u a hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u a hu
  have hsourceQ : ∀ u : ℤ, ∀ a : ℕ,
      (u,a) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l Q) →
      ramifiedWeight l ρ σ (u,a) ≤ ρ*rQ := by
    intro u a hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl Q ρ σ hdiv u a hu
  have htopP := ramifiedCutAut_weight_upper l hl ρ σ rP
    hρ hdiv hpos c (polynomialRamifiedLift l P) hsourceP
  have htopQ := ramifiedCutAut_weight_upper l hl ρ σ rQ
    hρ hdiv hpos c (polynomialRamifiedLift l Q) hsourceQ
  have holdP : ramifiedWeight l ρ σ E = ρ*rP := by
    simpa [E,rP,k,hMroot] using hsP.1.2
  have hOldQ : ramifiedWeight l ρ σ F = ρ*rQ := by
    simpa [F,rQ,k,← hN] using hsQ.1.2
  have hPstart : ∀ p ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)),
      ramifiedWeight l ρ σ p = ρ*rP → E.2 ≤ p.2 := by
    intro p hp hw
    have h := hsP.2 p.1 p.2 hp (by simpa [rP] using hw)
    simpa [E,hMroot] using h
  have hQstart : ∀ q ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)),
      ramifiedWeight l ρ σ q = ρ*rQ → F.2 ≤ q.2 := by
    intro q hq hw
    have h := hsQ.2 q.1 q.2 hq (by simpa [rQ] using hw)
    simpa [F,hN] using h
  obtain ⟨t,ht,hearly,hPface,hQface,hBP,hBQ⟩ :=
    ramified_exact_pair_exists_common_early_adjacent_face
      l hl ρ σ hρ hpos
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
      hexact (ρ*rP) (ρ*rQ) E F hpointP hpointQ
      holdP hOldQ hEgrade hFgrade hm2 hn2 hOld
      (by intro p hp; exact htopP p.1 p.2 hp)
      (by intro q hq; exact htopQ q.1 q.2 hq)
      hPstart hQstart
  refine ⟨c,hrootP,?_,?_⟩
  · exact hMroot.symm.trans hmP
  · refine ⟨t,ht,hearly,?_,?_,?_,?_⟩
    · simpa [E,hMroot,rP] using hPface
    · simpa [F,hN,rQ] using hQface
    · simpa [E,hMroot,rP] using hBP
    · simpa [F,hN,rQ] using hBQ

/-- At the selected maximum root, the common adjacent face can be
represented by a primitive positive-sum Newton direction. The only
remaining source premise here is the selected negative-grade bound. -/
theorem exactPair_maxRoot_cut_exists_primitive_common_face
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
  obtain ⟨c,hrootP,hmP,t,ht,hearly,hPface,hQface,
      ⟨BP,hBP,hBPlower,hBPtie⟩,
      ⟨BQ,hBQ,hBQlower,hBQtie⟩⟩ :=
    exactPair_maxRoot_cut_exists_common_early_adjacent_face
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ
      hQP hsum d n hd hn hweight hcop hPgrade
  obtain ⟨aP,bP,haP,_,_⟩ := Finset.one_lt_card_iff.mp hdirP
  obtain ⟨⟨iP,jP⟩,rfl⟩ := expo_surjective aP
  obtain ⟨aQ,bQ,haQ,_,_⟩ := Finset.one_lt_card_iff.mp hdirQ
  obtain ⟨⟨iQ,jQ⟩,rfl⟩ := expo_surjective aQ
  have hsP := polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hdir.2 iP jP haP c
  have hsQ := polynomialRamifiedCut_root_start_on_old_face
    l hl Q ρ σ hρ hdiv hdir.2 iQ jQ haQ c
  let M := (cutPoly ρ σ P.1).rootMultiplicity c
  let N := (cutPoly ρ σ Q.1).rootMultiplicity c
  let E : ℤ × ℕ :=
    (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
      ramifiedCutExponent l ρ σ*(M : ℤ),M)
  let F : ℤ × ℕ :=
    (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
      ramifiedCutExponent l ρ σ*(N : ℤ),N)
  have hEP : E ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) := hsP.1.1
  have hFQ : F ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) := hsQ.1.1
  have hEweight : ramifiedWeight l ρ σ E =
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := hsP.1.2
  have hFweight : ramifiedWeight l ρ σ F =
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1) := hsQ.1.2
  obtain ⟨R,S,hRdef,hSdef,hR,hsumRS,hPupperR,hQupperR,
      hEtopR,hFtopR,hBPtopR,hBQtopR⟩ :=
    ramified_common_rational_tilt_integral_face
      l hl ρ σ hρ
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
      (ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1))
      (ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1))
      E F BP BQ t hearly hEP hFQ hBP hBQ
      hEweight hFweight hPface hQface hBPtie hBQtie
  obtain ⟨r,s,g,hg,hRscale,hSscale,hdir',hr,
      hEtop,hFtop,hBPtop,hBQtop⟩ :=
    ramified_common_integral_face_primitive
      l hl R S hR hsumRS
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
      E F BP BQ hEP hFQ hPupperR hQupperR
      (hBPtopR.trans hEtopR.symm)
      (hBQtopR.trans hFtopR.symm)
  have hsneg : σ ≤ 0 → s < 0 := by
    intro hσ
    have hnum : 0 < t.num := Rat.num_pos.mpr ht
    have hden : (0 : ℤ) < t.den := by exact_mod_cast Rat.den_pos t
    have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
    have hprod : σ * (l : ℤ) * (t.den : ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hσ (le_of_lt hlZ))
        (le_of_lt hden)
    have hSneg : S < 0 := by
      rw [hSdef]
      change σ * (l : ℤ) * (t.den : ℤ) - t.num < 0
      omega
    by_contra hsbad
    have hsnon : 0 ≤ s := le_of_not_gt hsbad
    have hgnon : 0 ≤ g*s := mul_nonneg (le_of_lt hg) hsnon
    rw [← hSscale] at hgnon
    omega
  have hsourceP : ∀ u : ℤ, ∀ a : ℕ,
      (u,a) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
      ramifiedWeight l ρ σ (u,a) ≤
        ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    intro u a hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u a hu
  have hsourceQ : ∀ u : ℤ, ∀ a : ℕ,
      (u,a) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l Q) →
      ramifiedWeight l ρ σ (u,a) ≤
        ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1) := by
    intro u a hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl Q ρ σ hdiv u a hu
  have hPoldTop := ramifiedCutAut_weight_upper l hl ρ σ
    (((l : ℤ) / ρ) * vDeg ρ σ P.1) hρ hdiv hdir.2
    c (polynomialRamifiedLift l P) hsourceP
  have hQoldTop := ramifiedCutAut_weight_upper l hl ρ σ
    (((l : ℤ) / ρ) * vDeg ρ σ Q.1) hρ hdiv hdir.2
    c (polynomialRamifiedLift l Q) hsourceQ
  have hPend : ∀ p ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)),
      ramifiedWeight l r s p = ramifiedWeightDeg l hl r s
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) →
        E.1 - (l : ℤ)*(E.2 : ℤ) ≤
          p.1 - (l : ℤ)*(p.2 : ℤ) := by
    apply ramified_first_tilt_old_start_min_grade
      l hl ρ σ _
      (ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1)) E t ht
      hEweight
      (by intro p hp; exact hPoldTop p.1 p.2 hp)
      r s g hg (hRdef.symm.trans hRscale) (hSdef.symm.trans hSscale)
      hr hdir'.2 hEtop
  have hQend : ∀ q ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)),
      ramifiedWeight l r s q = ramifiedWeightDeg l hl r s
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) →
        F.1 - (l : ℤ)*(F.2 : ℤ) ≤
          q.1 - (l : ℤ)*(q.2 : ℤ) := by
    apply ramified_first_tilt_old_start_min_grade
      l hl ρ σ _
      (ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1)) F t ht
      hFweight
      (by intro q hq; exact hQoldTop q.1 q.2 hq)
      r s g hg (hRdef.symm.trans hRscale) (hSdef.symm.trans hSscale)
      hr hdir'.2 hFtop
  exact ⟨c,r,s,hrootP,hmP,hdir',hr,hsneg,hEtop,hFtop,hPend,hQend,
    ⟨BP,hBP,hBPlower,hBPtop⟩,
    ⟨BQ,hBQ,hBQlower,hBQtop⟩⟩

end Dixmier.Weyl
