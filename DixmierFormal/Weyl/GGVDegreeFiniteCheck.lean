/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# The finite arithmetic endpoint of G13 Corollary 7.4

The geometric reduction to these coordinates is not proved here. The finite
enumeration itself is exact and is kept separate from that source obligation.
-/

namespace Dixmier.Weyl

/-- Arithmetic part of the `μ < 1` step in G13 Proposition 7.3(4).
The weighted line through `C₀=(u,v)` and `C₁=(r,t)` lies above the
companion weight, so a proportional companion endpoint is proper. -/
theorem companion_endpoint_proper_of_weight
    (ρ σ u v r t f₁ f₂ : ℤ)
    (hρ : 0 < ρ) (hσ : σ < 0) (hsum : 0 < ρ + σ)
    (hu : 0 < u) (ht : 0 ≤ t) (hrt : t < r)
    (hline : ρ * u + σ * v = ρ * r + σ * t)
    (hcomp : ρ * f₁ + σ * f₂ = ρ + σ)
    (hprop : f₁ * v = f₂ * u) : f₁ < u := by
  have hwgt : ρ + σ < ρ * r + σ * t := by
    have hr : 1 ≤ r - t := by omega
    have hmul : ρ ≤ ρ * (r - t) := by nlinarith
    nlinarith
  have hcross : u * (ρ + σ) = f₁ * (ρ * u + σ * v) := by
    calc
      u * (ρ + σ) = u * (ρ * f₁ + σ * f₂) := by rw [hcomp]
      _ = f₁ * (ρ * u + σ * v) := by linear_combination -σ * hprop
  by_contra h
  have hf : u ≤ f₁ := by omega
  nlinarith [mul_nonneg (sub_nonneg.mpr hf) (le_of_lt hsum)]

/-- Both coordinates of the proportional companion endpoint are proper
once the main endpoint has positive coordinates. -/
theorem companion_endpoint_both_proper_of_weight
    (ρ σ u v r t f₁ f₂ : ℤ)
    (hρ : 0 < ρ) (hσ : σ < 0) (hsum : 0 < ρ + σ)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 ≤ t) (hrt : t < r)
    (hline : ρ * u + σ * v = ρ * r + σ * t)
    (hcomp : ρ * f₁ + σ * f₂ = ρ + σ)
    (hprop : f₁ * v = f₂ * u) : f₁ < u ∧ f₂ < v := by
  have hf₁ := companion_endpoint_proper_of_weight ρ σ u v r t f₁ f₂
    hρ hσ hsum hu ht hrt hline hcomp hprop
  constructor
  · exact hf₁
  · by_contra h
    have hf₂ : v ≤ f₂ := by omega
    nlinarith [mul_pos (sub_pos.mpr hf₁) hv,
      mul_nonneg (sub_nonneg.mpr hf₂) (le_of_lt hu)]

/-- Natural-coordinate adapter for the properness argument. Here the
direction is `(ρ,-k)` and the companion's weight is `ρ-k`. -/
theorem companion_endpoint_both_proper_nat
    (ρ k u v r s f₁ f₂ : ℕ)
    (hkpos : 0 < k) (hkρ : k < ρ) (hupos : 0 < u) (hvpos : 0 < v)
    (hsr : s < r)
    (hline : ρ * u + k * s = ρ * r + k * v)
    (hcomp : ρ * f₁ + k = k * f₂ + ρ)
    (hprop : f₁ * v = f₂ * u) : f₁ < u ∧ f₂ < v := by
  have hlineZ : (ρ : ℤ) * u + (-(k : ℤ)) * v =
      (ρ : ℤ) * r + (-(k : ℤ)) * s := by
    have hz : (ρ : ℤ) * u + (k : ℤ) * s =
        (ρ : ℤ) * r + (k : ℤ) * v := by exact_mod_cast hline
    nlinarith
  have hcompZ : (ρ : ℤ) * f₁ + (-(k : ℤ)) * f₂ =
      (ρ : ℤ) + (-(k : ℤ)) := by
    have hz : (ρ : ℤ) * f₁ + k = (k : ℤ) * f₂ + ρ := by
      exact_mod_cast hcomp
    nlinarith
  have hpropZ : (f₁ : ℤ) * v = (f₂ : ℤ) * u := by
    exact_mod_cast hprop
  have hproper := companion_endpoint_both_proper_of_weight
    (ρ : ℤ) (-(k : ℤ)) u v r s f₁ f₂
    (by exact_mod_cast (lt_trans hkpos hkρ))
    (by omega)
    (by omega) (by exact_mod_cast hupos) (by exact_mod_cast hvpos)
    (by omega) (by exact_mod_cast hsr) hlineZ hcompZ hpropZ
  exact_mod_cast hproper

/-- A proper integral point on the ray through `(u,v)` implies that
`(u,v)` is not primitive. This is the arithmetic step behind
G13 Proposition 7.3(3). -/
theorem proportional_lattice_point_not_coprime
    (u v f₁ f₂ : ℕ) (hfpos : 0 < f₁) (hflt : f₁ < u)
    (hprop : f₁ * v = f₂ * u) : ¬ Nat.Coprime u v := by
  intro hcop
  have hdiv : u ∣ f₁ * v := by
    refine ⟨f₂, ?_⟩
    simpa [mul_comm] using hprop
  have hudiv : u ∣ f₁ := hcop.dvd_of_dvd_mul_right hdiv
  have hle := Nat.le_of_dvd hfpos hudiv
  omega

/-- In the same situation, the gcd is strictly larger than one. -/
theorem proportional_lattice_point_gcd_gt_one
    (u v f₁ f₂ : ℕ) (hfpos : 0 < f₁) (hflt : f₁ < u)
    (hprop : f₁ * v = f₂ * u) :
    1 < Nat.gcd u v := by
  have hgpos : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_left v (by omega)
  by_contra h
  have hgone : Nat.gcd u v = 1 := by omega
  exact proportional_lattice_point_not_coprime u v f₁ f₂ hfpos hflt hprop
    (by simpa [Nat.Coprime] using hgone)

/-- The primitive direction through the companion endpoint and `(1,1)`
automatically gives the companion's weight equation. -/
theorem gcd_normalized_direction_companion_weight
    (f₁ f₂ : ℕ) (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) :
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ := (f₂ - 1) / d
    let k := (f₁ - 1) / d
    ρ * f₁ + k = k * f₂ + ρ := by
  dsimp
  set d := Nat.gcd (f₁ - 1) (f₂ - 1)
  set ρ := (f₂ - 1) / d
  set k := (f₁ - 1) / d
  have ha : k * d = f₁ - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hb : ρ * d = f₂ - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hcross : ρ * (f₁ - 1) = k * (f₂ - 1) := by
    rw [← ha, ← hb]
    ring
  have hf₁eq : f₁ - 1 + 1 = f₁ := by omega
  have hf₂eq : f₂ - 1 + 1 = f₂ := by omega
  nlinarith

/-- A proper positive proportional endpoint on a ray with `u<v`
determines a strict negative-crossing primitive direction. -/
theorem gcd_normalized_direction_strict
    (u v f₁ f₂ : ℕ) (huv : u < v)
    (hf₁ : 2 ≤ f₁) (hprop : f₁ * v = f₂ * u) :
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    0 < (f₁ - 1) / d ∧
      (f₁ - 1) / d < (f₂ - 1) / d := by
  have hf₂gt : f₁ < f₂ := by
    by_contra h
    have hle : f₂ ≤ f₁ := by omega
    have hdifference : 0 < f₁ * (v - u) :=
      mul_pos (by omega) (by omega)
    have hnonneg : 0 ≤ (f₁ - f₂) * u := Nat.zero_le _
    nlinarith
  set d := Nat.gcd (f₁ - 1) (f₂ - 1)
  set k := (f₁ - 1) / d
  set ρ := (f₂ - 1) / d
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have ha : k * d = f₁ - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hb : ρ * d = f₂ - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  change 0 < k ∧ k < ρ
  constructor
  · have hk_ne : k ≠ 0 := by
      intro hz
      rw [hz] at ha
      simp at ha
      omega
    exact Nat.pos_of_ne_zero hk_ne
  · by_contra h
    have hle : ρ ≤ k := by omega
    have hmul := Nat.mul_le_mul_right d hle
    omega

def smallPairs : Finset (ℕ × ℕ) :=
  ((Finset.range 16).product (Finset.range 16)).filter fun p =>
    2 < p.1 ∧ p.1 < p.2 ∧ p.1 + p.2 ≤ 15

def factorPairs : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (smallPairs.product ((Finset.range 16).product (Finset.range 16))).filter fun p =>
    2 ≤ p.2.1 ∧ p.2.1 < p.1.1 ∧ p.2.2 < p.1.2 ∧
      p.2.1 * p.1.2 = p.2.2 * p.1.1

/-- The thirteen proportional-point rows listed before the preceding-point
test in G13 Corollary 7.4. -/
theorem ggvSmallDegreeFactorPairs_eq :
    factorPairs =
      {((3, 6), (2, 4)),
       ((3, 9), (2, 6)),
       ((3, 12), (2, 8)),
       ((4, 6), (2, 3)),
       ((4, 8), (2, 4)),
       ((4, 8), (3, 6)),
       ((4, 10), (2, 5)),
       ((5, 10), (2, 4)),
       ((5, 10), (3, 6)),
       ((5, 10), (4, 8)),
       ((6, 8), (3, 4)),
       ((6, 9), (2, 3)),
       ((6, 9), (4, 6))} := by
  decide

/-- The last finite coordinate test in G13 Corollary 7.4, before the
forbidden-corner calculation. The nested pairs are `((u,v),(f₁,f₂)),(r,s)`. -/
def ggvSmallDegreeCandidates : Finset (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) :=
  (factorPairs.product ((Finset.range 16).product (Finset.range 16))).filter fun p =>
    let u := p.1.1.1
    let v := p.1.1.2
    let f₁ := p.1.2.1
    let f₂ := p.1.2.2
    let r := p.2.1
    let s := p.2.2
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ := (f₂ - 1) / d
    let t := (f₁ - 1) / d
    s < r ∧ r < u ∧ ρ * u + t * s = ρ * r + t * v

/-- The source's small-degree search has exactly five surviving coordinate
configurations before its final corner exclusions. -/
theorem ggvSmallDegreeCandidates_eq :
    ggvSmallDegreeCandidates =
      {((((3, 6), (2, 4)), (1, 0))),
       ((((4, 6), (2, 3)), (1, 0))),
       ((((5, 10), (2, 4)), (2, 1))),
       ((((5, 10), (3, 6)), (1, 0))),
       ((((6, 9), (2, 3)), (2, 1)))} := by
  decide

/-- Every remaining row gives the normalized forbidden corner of G13:
`C₂=(h-1/ρ,h)` with `h≥2`. The equations are cleared of denominators. -/
theorem ggvSmallDegreeCandidates_forbidden_corner
    (p : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ))
    (hp : p ∈ ggvSmallDegreeCandidates) :
    let v := p.1.1.2
    let f₁ := p.1.2.1
    let f₂ := p.1.2.2
    let r := p.2.1
    let s := p.2.2
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ := (f₂ - 1) / d
    let t := (f₁ - 1) / d
    d = 1 ∧ 0 < ρ ∧
      ∃ h : ℕ, 2 ≤ h ∧ s ≤ h ∧ v = s + ρ * h ∧
        ρ * r + (h - s) * t = ρ * h - 1 := by
  rw [ggvSmallDegreeCandidates_eq] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h
  · subst p; norm_num; exact ⟨2, by norm_num⟩
  · subst p; norm_num; exact ⟨3, by norm_num⟩
  · subst p; norm_num; exact ⟨3, by norm_num⟩
  · subst p; norm_num; exact ⟨2, by norm_num⟩
  · subst p; norm_num; exact ⟨4, by norm_num⟩

/-- The finite table as a reusable arithmetic exclusion. Any coordinates
satisfying the listed small-degree hypotheses land on a forbidden corner. -/
theorem ggv_small_degree_coordinates_forbidden_corner
    (u v f₁ f₂ r s : ℕ)
    (huv : u < v) (hdegree : u + v ≤ 15)
    (hf₁ : 2 ≤ f₁)
    (hproportional : f₁ * v = f₂ * u)
    (hsr : s < r) (hru : r < u)
    (hweight :
      let d := Nat.gcd (f₁ - 1) (f₂ - 1)
      let ρ := (f₂ - 1) / d
      let t := (f₁ - 1) / d
      ρ * u + t * s = ρ * r + t * v) :
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ := (f₂ - 1) / d
    let t := (f₁ - 1) / d
    d = 1 ∧ 0 < ρ ∧
      ∃ h : ℕ, 2 ≤ h ∧ s ≤ h ∧ v = s + ρ * h ∧
        ρ * r + (h - s) * t = ρ * h - 1 := by
  have huPos : 0 < u := by
    by_contra hn
    have hz : u = 0 := by omega
    rw [hz] at hproportional
    nlinarith
  have hf₂pos : 0 < f₂ := by
    by_contra h
    have hz : f₂ = 0 := by omega
    rw [hz] at hproportional
    nlinarith
  have hcomp := gcd_normalized_direction_companion_weight
    f₁ f₂ (by omega) hf₂pos
  obtain ⟨hdirpos, hdirlt⟩ :=
    gcd_normalized_direction_strict u v f₁ f₂ huv hf₁ hproportional
  obtain ⟨hfproper, hf₂⟩ := companion_endpoint_both_proper_nat
    ((f₂ - 1) / Nat.gcd (f₁ - 1) (f₂ - 1))
    ((f₁ - 1) / Nat.gcd (f₁ - 1) (f₂ - 1))
    u v r s f₁ f₂ hdirpos hdirlt huPos (by omega)
    hsr hweight hcomp hproportional
  have hu : 2 < u := by omega
  have hp : ((((u, v), (f₁, f₂)), (r, s))) ∈
      ggvSmallDegreeCandidates := by
    have hbounds : u < 16 ∧ v < 16 ∧ f₁ < 16 ∧ f₂ < 16 ∧
        r < 16 ∧ s < 16 := by omega
    rcases hbounds with ⟨hu16, hv16, hf₁16, hf₂16, hr16, hs16⟩
    simp [ggvSmallDegreeCandidates, factorPairs, smallPairs,
      hu, huv, hdegree, hf₁, hfproper, hf₂, hproportional,
      hsr, hru, hweight, hu16, hv16, hf₁16, hf₂16, hr16, hs16]
  exact ggvSmallDegreeCandidates_forbidden_corner _ hp

end Dixmier.Weyl
