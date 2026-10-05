/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialRamifiedFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Transfer of the maximum-root cut endpoint to a polynomial Weyl source

The source PBW support and its top weighted face are transported through
the injective algebra homomorphism and the cut-polynomial identity.
-/
namespace Dixmier.Weyl

theorem polynomialPBW_weight_le_vDeg (P : A1 ℂ)
    (ρ σ : ℤ) (i j : ℕ)
    (hmem : expo i j ∈ (symbol P.1).support) :
    (i : ℤ) * ρ + (j : ℤ) * σ ≤ vDeg ρ σ P.1 := by
  have hle :
      (↑(Finsupp.weight (wt ρ σ) (expo i j)) : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) := by
    exact Finset.le_sup
      (f := fun d => (↑(Finsupp.weight (wt ρ σ) d) : WithBot ℤ)) hmem
  have hnotbot :
      MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) ≠ ⊥ := by
    intro hz
    have hzero :=
      (MvPolynomial.weightedTotalDegree'_eq_bot_iff
        (wt ρ σ) (symbol P.1)).mp hz
    rw [hzero] at hmem
    simp at hmem
  have hle' : Finsupp.weight (wt ρ σ) (expo i j) ≤
      WithBot.unbotD 0
        (MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1)) :=
    (WithBot.le_unbotD_iff hnotbot).mpr hle
  simpa [vDeg, expo_weight] using hle'

theorem polynomialRamifiedLift_weight_le_scaled_vDeg
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hdiv : ρ ∣ (l : ℤ))
    (u : ℤ) (n : ℕ)
    (hmem : (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P)) :
    ramifiedWeight l ρ σ (u,n) ≤
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
  obtain ⟨i,hu,hs⟩ :=
    (polynomialRamifiedLift_support_iff_symbol l hl P u n).mp hmem
  have hle := polynomialPBW_weight_le_vDeg P ρ σ i n hs
  have hlz : (0 : ℤ) ≤ (l : ℤ) := by exact_mod_cast Nat.zero_le l
  have hmul := mul_le_mul_of_nonneg_left hle hlz
  have hr :
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) =
        (l : ℤ) * vDeg ρ σ P.1 := by
    calc
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) =
        (ρ * ((l : ℤ) / ρ)) * vDeg ρ σ P.1 := by ring
      _ = (l : ℤ) * vDeg ρ σ P.1 := by
        rw [Int.mul_ediv_cancel' hdiv]
  rw [hu, polynomialRamifiedLift_weight_scaled, hr]
  simpa only [expo_weight] using hmul
theorem polynomialFace_point_source_data (P : A1 ℂ)
    (ρ σ : ℤ) (i j : ℕ)
    (hface : expo i j ∈ (leadingForm ρ σ P.1).support) :
    expo i j ∈ (symbol P.1).support ∧
      (i : ℤ) * ρ + (j : ℤ) * σ = vDeg ρ σ P.1 := by
  have hs : expo i j ∈ (symbol P.1).support :=
    weightedComponent_support_subset (symbol P.1)
      ρ σ (vDeg ρ σ P.1) hface
  have hhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hw := hhom (MvPolynomial.mem_support_iff.mp hface)
  rw [expo_weight] at hw
  exact ⟨hs,hw⟩

theorem polynomialRamifiedLift_face_point (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) (ρ σ : ℤ) (hdiv : ρ ∣ (l : ℤ))
    (i j : ℕ)
    (hface : expo i j ∈ (leadingForm ρ σ P.1).support) :
    (((l : ℤ) * (i : ℤ)),j) ∈
      ramifiedPBWSupport l hl (polynomialRamifiedLift l P) ∧
    ramifiedWeight l ρ σ (((l : ℤ) * (i : ℤ)),j) =
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
  obtain ⟨hs,hw⟩ := polynomialFace_point_source_data P ρ σ i j hface
  have hmem :
      (((l : ℤ) * (i : ℤ)),j) ∈
        ramifiedPBWSupport l hl (polynomialRamifiedLift l P) := by
    apply (polynomialRamifiedLift_support_iff_symbol l hl P _ j).mpr
    exact ⟨i,rfl,hs⟩
  refine ⟨hmem,?_⟩
  rw [polynomialRamifiedLift_weight_scaled, expo_weight, hw]
  calc
    (l : ℤ) * vDeg ρ σ P.1 =
      (ρ * ((l : ℤ) / ρ)) * vDeg ρ σ P.1 := by
        rw [Int.mul_ediv_cancel' hdiv]
    _ = ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by ring

/-- A genuine two-point polynomial face admits a maximum-root shear,
whose selected endpoint is expressed with the paper's cut polynomial.
This is the source-to-ramified endpoint transfer, not yet the G13 new
direction or forbidden-corner conclusion. -/
theorem polynomialRamifiedCut_exists_maxRoot_start_of_two_face_points
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (i₁ i₂ j₁ j₂ : ℕ)
    (h₁ : expo i₁ j₁ ∈ (leadingForm ρ σ P.1).support)
    (h₂ : expo i₂ j₂ ∈ (leadingForm ρ σ P.1).support)
    (hdist : (i₁,j₁) ≠ (i₂,j₂)) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (((((l : ℤ) / ρ) * vDeg ρ σ P.1) -
          ramifiedCutExponent l ρ σ *
            (maxRootMult (cutPoly ρ σ P.1) : ℤ),
        maxRootMult (cutPoly ρ σ P.1)) ∈
          ramifiedPBWSupport l hl
            (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))) := by
  let r : ℤ := ((l : ℤ) / ρ) * vDeg ρ σ P.1
  obtain ⟨hs₁,hw₁⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i₁ j₁ h₁
  obtain ⟨hs₂,hw₂⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i₂ j₂ h₂
  have hdistinct :
      (((l : ℤ) * (i₁ : ℤ)),j₁) ≠
        (((l : ℤ) * (i₂ : ℤ)),j₂) := by
    intro he
    have hi : (l : ℤ) * (i₁ : ℤ) =
        (l : ℤ) * (i₂ : ℤ) := (Prod.mk.inj he).1
    have hj : j₁ = j₂ := (Prod.mk.inj he).2
    have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
    have hii : i₁ = i₂ := by
      have hz := (mul_left_cancel₀ hlz) hi
      exact_mod_cast hz
    exact hdist (Prod.ext hii hj)
  have hbound : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r := by
    intro u n hm
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hm
  obtain ⟨c,hroot,hm,hpoint⟩ :=
    ramifiedCutAut_exists_maxRoot_start_of_two_points
      l hl ρ σ r ((l : ℤ) * (i₁ : ℤ))
      ((l : ℤ) * (i₂ : ℤ)) j₁ j₂
      hρ hdiv hpos (polynomialRamifiedLift l P)
      hs₁ hs₂ hw₁ hw₂ hdistinct hbound
  refine ⟨c,?_,?_,?_⟩
  · simpa only [r, polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]
      using hroot
  · simpa only [r, polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]
      using hm
  · simpa only [r,
      polynomialRamifiedFace_maxRootMult_eq_cutPoly l hl P ρ σ hρ hdiv]
      using hpoint

/-- The polynomial source direction itself supplies the two distinct
face points needed by the maximum-root selection theorem. -/
theorem polynomialRamifiedCut_exists_maxRoot_start_of_InDir
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hdir : InDir ρ σ P.1) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (((((l : ℤ) / ρ) * vDeg ρ σ P.1) -
          ramifiedCutExponent l ρ σ *
            (maxRootMult (cutPoly ρ σ P.1) : ℤ),
        maxRootMult (cutPoly ρ σ P.1)) ∈
          ramifiedPBWSupport l hl
            (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))) := by
  obtain ⟨d₁,d₂,hd₁,hd₂,hne⟩ :=
    Finset.one_lt_card_iff.mp hdir
  obtain ⟨⟨i₁,j₁⟩,rfl⟩ := expo_surjective d₁
  obtain ⟨⟨i₂,j₂⟩,rfl⟩ := expo_surjective d₂
  have hdist : (i₁,j₁) ≠ (i₂,j₂) := by
    intro he
    exact hne (congrArg (fun p : ℕ × ℕ => expo p.1 p.2) he)
  exact polynomialRamifiedCut_exists_maxRoot_start_of_two_face_points
    l hl P ρ σ hρ hdiv hpos i₁ i₂ j₁ j₂ hd₁ hd₂ hdist

/-- For a chosen root, the source-level cut has no point preceding its
root-multiplicity endpoint on the old face. This is an exact PBW statement,
not yet the assertion that a new supporting direction exists. -/
theorem polynomialRamifiedCut_root_start_on_old_face
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (i j : ℕ)
    (hface : expo i j ∈ (leadingForm ρ σ P.1).support)
    (c : ℂ) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c (cutPoly ρ σ P.1)
    ((r-k*(m : ℤ),m) ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      ramifiedWeight l ρ σ (r-k*(m : ℤ),m) = ρ*r) ∧
    (∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) →
      ramifiedWeight l ρ σ (u,n) = ρ*r → m ≤ n) := by
  obtain ⟨hmem,htop⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i j hface
  have hbound : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
        ramifiedWeight l ρ σ (u,n) ≤
          ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    intro u n hm
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hm
  simpa only [polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]
    using ramifiedCutAut_root_start_on_old_face l hl ρ σ
      (((l : ℤ) / ρ) * vDeg ρ σ P.1)
      ((l : ℤ) * (i : ℤ)) j hρ hdiv hpos c
      (polynomialRamifiedLift l P) hmem htop hbound

/-- The selected old-face endpoint also maximizes the scaled PBW grade. -/
theorem polynomialRamifiedCut_root_start_max_grade
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (i j : ℕ)
    (hface : expo i j ∈ (leadingForm ρ σ P.1).support)
    (c : ℂ) (u : ℤ) (n : ℕ)
    (hun : (u,n) ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)))
    (hwn : ramifiedWeight l ρ σ (u,n) =
      ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1)) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c (cutPoly ρ σ P.1)
    u - (l : ℤ)*(n : ℤ) ≤
      (r-k*(m : ℤ)) - (l : ℤ)*(m : ℤ) := by
  obtain ⟨hmem,htop⟩ :=
    polynomialRamifiedLift_face_point l hl P ρ σ hdiv i j hface
  have hbound : ∀ v : ℤ, ∀ a : ℕ,
      (v,a) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
        ramifiedWeight l ρ σ (v,a) ≤
          ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    intro v a hm
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv v a hm
  simpa only [polynomialRamifiedFace_eq_cutPoly l hl P ρ σ hρ hdiv]
    using ramifiedCutAut_root_start_max_grade l hl ρ σ
      (((l : ℤ) / ρ) * vDeg ρ σ P.1)
      ((l : ℤ) * (i : ℤ)) j hρ hdiv hpos c
      (polynomialRamifiedLift l P) hmem htop hbound u n hun hwn

/-- A maximum-multiplicity root of the actual source cut polynomial
selects an occupied old-face endpoint that precedes every other point
in derivative order and maximizes the scaled PBW grade. -/
theorem polynomialRamifiedCut_exists_maxRoot_extremal_of_InDir
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hdir : InDir ρ σ P.1) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let k := ramifiedCutExponent l ρ σ
    let M := maxRootMult (cutPoly ρ σ P.1)
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c = M ∧
      (r-k*(M : ℤ),M) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      (∀ u : ℤ, ∀ n : ℕ,
        (u,n) ∈ ramifiedPBWSupport l hl
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) →
        ramifiedWeight l ρ σ (u,n) = ρ*r →
        M ≤ n ∧
        u - (l : ℤ)*(n : ℤ) ≤
          (r-k*(M : ℤ)) - (l : ℤ)*(M : ℤ)) := by
  obtain ⟨c,hroot,hm,hpoint⟩ :=
    polynomialRamifiedCut_exists_maxRoot_start_of_InDir
      l hl P ρ σ hρ hdiv hpos hdir
  obtain ⟨d₁,d₂,hd₁,hd₂,hne⟩ := Finset.one_lt_card_iff.mp hdir
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d₁
  refine ⟨c,hroot,hm,hpoint,?_⟩
  intro u n hun hwn
  have hs := polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hpos i j hd₁ c
  have hmin := hs.2 u n hun hwn
  have hgrade := polynomialRamifiedCut_root_start_max_grade
    l hl P ρ σ hρ hdiv hpos i j hd₁ c u n hun hwn
  rw [hm] at hmin hgrade
  exact ⟨hmin,hgrade⟩

/-- The same maximum-root shear gives the extremal endpoint of `P`
and transports its unrestricted exact mate through the Weyl relation. -/
theorem polynomialRamifiedCut_exact_pair_maxRoot_extremal
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hdir : InDir ρ σ P.1)
    (hQP : Q * P - P * Q = 1) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let k := ramifiedCutExponent l ρ σ
    let M := maxRootMult (cutPoly ρ σ P.1)
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c = M ∧
      (r-k*(M : ℤ),M) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      (∀ u : ℤ, ∀ n : ℕ,
        (u,n) ∈ ramifiedPBWSupport l hl
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) →
        ramifiedWeight l ρ σ (u,n) = ρ*r →
        M ≤ n ∧
        u - (l : ℤ)*(n : ℤ) ≤
          (r-k*(M : ℤ)) - (l : ℤ)*(M : ℤ)) ∧
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 := by
  obtain ⟨c,hroot,hm,hpoint,hext⟩ :=
    polynomialRamifiedCut_exists_maxRoot_extremal_of_InDir
      l hl P ρ σ hρ hdiv hpos hdir
  refine ⟨c,hroot,hm,hpoint,hext,?_⟩
  apply ramifiedCutAut_exact_pair
  exact polynomialRamifiedLift_bracket_one l hl P Q hQP

/-- The selected polynomial-source cut acts on both members of an
exact Weyl pair. The chosen root and endpoint come from `P`; the exact
commutator survives for the unrestricted mate `Q`. -/
theorem polynomialRamifiedCut_exact_pair_maxRoot_start
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (hdir : InDir ρ σ P.1)
    (hQP : Q * P - P * Q = 1) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (((((l : ℤ) / ρ) * vDeg ρ σ P.1) -
          ramifiedCutExponent l ρ σ *
            (maxRootMult (cutPoly ρ σ P.1) : ℤ),
        maxRootMult (cutPoly ρ σ P.1)) ∈
          ramifiedPBWSupport l hl
            (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))) ∧
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 := by
  obtain ⟨c,hroot,hm,hpoint⟩ :=
    polynomialRamifiedCut_exists_maxRoot_start_of_InDir
      l hl P ρ σ hρ hdiv hpos hdir
  refine ⟨c,hroot,hm,hpoint,?_⟩
  apply ramifiedCutAut_exact_pair
  exact polynomialRamifiedLift_bracket_one l hl P Q hQP

end Dixmier.Weyl
