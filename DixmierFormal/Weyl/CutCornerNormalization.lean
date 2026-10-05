/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CounterexampleCutFace
public import DixmierFormal.Weyl.RamifiedOriginStripping
public import DixmierFormal.Weyl.GGVStrictNegativeCornerFrontier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Normalized coordinates of the maximum-root cut

The rational coordinates in the polynomial source contract determine the
integer PBW coordinates at coefficient index equal to the first direction
coordinate. These identities concern the actual selected root endpoint.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

theorem normalized_cut_corner_coordinates
    (P : A1 ℂ) (ρ σ : ℤ) (u v m d h : ℕ)
    (hρ : 0 < ρ) (hd : 0 < d)
    (hpoint : expo u v ∈ (leadingForm ρ σ P.1).support)
    (hcorner :
      ((u : ℚ) + ((v : ℚ) - m) * σ / ρ) / d = h - 1 / ρ ∧
        (m : ℚ) / d = h) :
    m = d * h ∧
      vDeg ρ σ P.1 - σ * (m : ℤ) =
        (d : ℤ) * ((h : ℤ) * ρ - 1) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hρQ : (ρ : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hmQ := (div_eq_iff hdQ).mp hcorner.2
  have hm : m = d * h := by
    exact_mod_cast (by nlinarith only [hmQ] : (m : ℚ) = (d : ℚ) * h)
  have hfirst := hcorner.1
  field_simp [hdQ, hρQ] at hfirst
  have hfirstQ : (u : ℚ) * ρ + ((v : ℚ) - m) * σ =
      (d : ℚ) * ((h : ℚ) * ρ - 1) := by
    nlinarith only [hfirst]
  have hfirstZ : (u : ℤ) * ρ + ((v : ℤ) - m) * σ =
      (d : ℤ) * ((h : ℤ) * ρ - 1) := by exact_mod_cast hfirstQ
  have hw := (polynomialFace_point_source_data P ρ σ u v hpoint).2
  refine ⟨hm, ?_⟩
  nlinarith only [hw, hfirstZ]

/-- The coordinates hold for every root realizing the maximum order,
so they can be attached to the same witness as the common cut face. -/
theorem normalized_maxRoot_cut_endpoint
    (l : ℕ) (P : A1 ℂ) (ρ σ : ℤ) (u v d h : ℕ) (c : ℂ)
    (hρ : 0 < ρ) (hρl : (l : ℤ) = ρ) (hd : 0 < d)
    (hpoint : expo u v ∈ (leadingForm ρ σ P.1).support)
    (hc : (cutPoly ρ σ P.1).rootMultiplicity c =
      maxRootMult (cutPoly ρ σ P.1))
    (hcorner :
      ((u : ℚ) + ((v : ℚ) - maxRootMult (cutPoly ρ σ P.1)) * σ / ρ) / d =
          h - 1 / ρ ∧
        (maxRootMult (cutPoly ρ σ P.1) : ℚ) / d = h) :
    let M := (cutPoly ρ σ P.1).rootMultiplicity c
    ((((l : ℤ) / ρ) * vDeg ρ σ P.1 -
        ramifiedCutExponent l ρ σ * (M : ℤ), M) : ℤ × ℕ) =
      ((d : ℤ) * ((h : ℤ) * (l : ℤ) - 1), d * h) := by
  obtain ⟨hm, hx⟩ := normalized_cut_corner_coordinates
    P ρ σ u v (maxRootMult (cutPoly ρ σ P.1)) d h hρ hd hpoint hcorner
  have hself : (l : ℤ) / ρ = 1 := by
    rw [hρl]
    exact Int.ediv_self (ne_of_gt hρ)
  have hk : ramifiedCutExponent l ρ σ = σ := by
    simp [ramifiedCutExponent, hself]
  dsimp
  apply Prod.ext
  · simpa only [hself, one_mul, hk, hc, hρl,
      Int.ediv_self (ne_of_gt hρ)] using hx
  · exact hc.trans hm

/-- A polynomial source with the forbidden rational normalization yields
an exact ramified pair at a genuine common negative direction. All
coordinates and inequalities concern the same selected root and direction. -/
theorem counterexample_normalized_cut_corner_configuration
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) (hρl : (l : ℤ) = ρ)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (u v d n h : ℕ) (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) = vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hneg : ∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0)
    (hpoint : expo u v ∈ (leadingForm ρ σ P.1).support)
    (hcorner :
      ((u : ℚ) + ((v : ℚ) - maxRootMult (cutPoly ρ σ P.1)) * σ / ρ) / d =
          h - 1 / ρ ∧
        (maxRootMult (cutPoly ρ σ P.1) : ℚ) / d = h) :
    ∃ c : ℂ, ∃ r s : ℤ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c = maxRootMult (cutPoly ρ σ P.1) ∧
      IsDirection r s ∧ 0 < r ∧ s < 0 ∧
      let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
      let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
      let N := (cutPoly ρ σ Q.1).rootMultiplicity c
      let E : ℤ × ℕ := ((d : ℤ) * ((h : ℤ) * (l : ℤ) - 1), d * h)
      let G : ℤ × ℕ :=
        (((l : ℤ) / ρ) * vDeg ρ σ Q.1 - ramifiedCutExponent l ρ σ * (N : ℤ), N)
      E ∈ ramifiedPBWSupport l hl U ∧
      G ∈ ramifiedPBWSupport l hl V ∧
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s U ∧
      ramifiedWeight l r s G = ramifiedWeightDeg l hl r s V ∧
      0 < ramifiedWeightDeg l hl r s U ∧
      0 < ramifiedWeightDeg l hl r s V ∧
      ramifiedWeightDeg l hl r s V * (d : ℤ) =
        ramifiedWeightDeg l hl r s U * (n : ℤ) ∧
      ¬ (ramifiedWeightDeg l hl r s U ∣ ramifiedWeightDeg l hl r s V) ∧
      ¬ (ramifiedWeightDeg l hl r s V ∣ ramifiedWeightDeg l hl r s U) ∧
      (l : ℤ) * (r + s) <
        ramifiedWeightDeg l hl r s U + ramifiedWeightDeg l hl r s V ∧
      V * U - U * V = 1 ∧
      E.1 - (l : ℤ) * (E.2 : ℤ) < 0 ∧
      G.1 - (l : ℤ) * (G.2 : ℤ) < 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        ramifiedWeight l r s p = ramifiedWeightDeg l hl r s U →
          E.1 - (l : ℤ) * (E.2 : ℤ) ≤ p.1 - (l : ℤ) * (p.2 : ℤ)) ∧
      (∀ q ∈ ramifiedPBWSupport l hl V,
        ramifiedWeight l r s q = ramifiedWeightDeg l hl r s V →
          G.1 - (l : ℤ) * (G.2 : ℤ) ≤ q.1 - (l : ℤ) * (q.2 : ℤ)) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl U, BP.2 < d * h ∧
        ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s U) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl V, BQ.2 < N ∧
        ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s V) := by
  have hdiv : ρ ∣ (l : ℤ) := by rw [hρl]
  obtain ⟨c, r, s, hc, hm, hnewdir, hr, hs, hEtop, hGtop,
      hUpos, hVpos, hratio, hEgrade, hGgrade, hEmin, hGmin, hBP, hBQ⟩ :=
    counterexample_maxRoot_cut_positive_ratio
      l hl P Q hpair ρ σ hdir hρ hdiv hdirP hdirQ hsum
      d n (by omega) (by omega) hweight hcop hneg
  have hcoord := normalized_maxRoot_cut_endpoint
    l P ρ σ u v d h c hρ hρl (by omega) hpoint hm hcorner
  have hmorder : (cutPoly ρ σ P.1).rootMultiplicity c = d * h :=
    congrArg Prod.snd hcoord
  have hEpoint := (polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hdir.2 u v hpoint c).1.1
  obtain ⟨e, _, he, _, _⟩ := Finset.one_lt_card_iff.mp hdirQ
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective e
  have hGpoint := (polynomialRamifiedCut_root_start_on_old_face
    l hl Q ρ σ hρ hdiv hdir.2 i j he c).1.1
  rw [hcoord] at hEpoint hEtop hEgrade hEmin
  rw [hmorder] at hBP
  have hexact := ramifiedCutAut_exact_pair l hl ρ σ c _ _
    (polynomialRamifiedLift_bracket_one l hl P Q hpair.1)
  have hstrict := ramified_corner_exact_pair_weight_sum_strict
    l hl r s hr hnewdir.2
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
    ((d : ℤ) * ((h : ℤ) * (l : ℤ) - 1), d * h)
    hEtop d n h hd hn hh rfl rfl hUpos hratio hexact
  have hnondiv := coprime_positive_weight_ratio_neither_dvd
    _ _ hUpos hVpos n d hn hd hcop hratio
  exact ⟨c, r, s, hc, hm, hnewdir, hr, hs hσ, hEpoint, hGpoint,
    hEtop, hGtop, hUpos, hVpos, hratio, hnondiv.1, hnondiv.2, hstrict, hexact,
    hEgrade, hGgrade, hEmin, hGmin, hBP, hBQ⟩

end Dixmier.Weyl
