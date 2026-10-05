/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeCutMultiplicity
public import DixmierFormal.Weyl.GGVCutCornerProved
public import DixmierFormal.Weyl.GGVStrictNegativeCornerFrontier
public import DixmierFormal.Weyl.NegativeCrossingProperPower

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exclusion of the actual small-degree crossing configuration -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1200000

theorem smallDegreeCrossing_impossible
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) : False := by
  have hρ : (0 : ℤ) < H.rho := by exact_mod_cast H.rhoPos
  have hs : (0 : ℤ) < H.s := by exact_mod_cast H.sPos
  have hsumDir : (0 : ℤ) < (H.rho : ℤ)-H.s := by have := H.direction.2; omega
  have hd : (1 : ℤ) < H.d := by exact_mod_cast H.dProper
  have hn : (1 : ℤ) < H.n := by exact_mod_cast H.nProper
  have hstartGrade : 0 < grade (expo H.r H.t) := by
    simp [grade,expo]; exact_mod_cast H.startCrossing
  have hwge := positive_grade_weight_ge_rho H.rho (-(H.s : ℤ))
    (expo H.r H.t) hρ (by simpa using hsumDir) hstartGrade
  have hwstart := H.rootHomogeneous (mem_support_iff.mp H.startOccupied)
  rw [hwstart] at hwge
  have hwpos : 0 < H.weight := lt_of_lt_of_le hρ hwge
  have hwQ : vDeg H.rho (-(H.s : ℤ)) H.right.1=(H.n : ℤ)*H.weight := by
    have h := leadingFace_root_power_weight H.right H.root H.mu H.rho H.s
      H.n H.u H.v H.weight H.rootNonzero H.muNonzero H.sPos H.rootHomogeneous
      H.endOccupied H.endMax H.rightFace
    have he := H.rootHomogeneous (mem_support_iff.mp H.endOccupied)
    rw [expo_weight] at he
    nlinarith
  have hpPos : 0 < vDeg H.rho (-(H.s : ℤ)) H.left.1 := by
    rw [H.leftWeight]; exact mul_pos (by omega) hwpos
  have hqPos : 0 < vDeg H.rho (-(H.s : ℤ)) H.right.1 := by
    rw [hwQ]; exact mul_pos (by omega) hwpos
  have hthreshold : (H.rho : ℤ)+(-(H.s : ℤ)) <
      vDeg H.rho (-(H.s : ℤ)) H.left.1+vDeg H.rho (-(H.s : ℤ)) H.right.1 := by
    rw [H.leftWeight,hwQ]; nlinarith
  have hratio : vDeg H.rho (-(H.s : ℤ)) H.right.1*(H.d : ℤ)=
      vDeg H.rho (-(H.s : ℤ)) H.left.1*(H.n : ℤ) := by
    rw [H.leftWeight,hwQ]; ring
  have hcop := H.coprime.symm
  obtain ⟨hnd1,hnd2⟩ := coprime_positive_weight_ratio_neither_dvd
    _ _ hpPos hqPos H.n H.d H.nProper H.dProper hcop hratio
  obtain ⟨hPend,hPstart,hPmax,hPmin⟩ := leadingFace_power_endpoint_pair
    H.left H.root H.nu H.rho H.s H.d H.u H.v H.r H.t H.weight
      H.rootNonzero H.nuNonzero H.sPos H.rootHomogeneous H.endOccupied
      H.startOccupied H.endMax H.startMin H.leftFace
  obtain ⟨hQend,hQstart,hQmax,hQmin⟩ := leadingFace_power_endpoint_pair
    H.right H.root H.mu H.rho H.s H.n H.u H.v H.r H.t H.weight
      H.rootNonzero H.muNonzero H.sPos H.rootHomogeneous H.endOccupied
      H.startOccupied H.endMax H.startMin H.rightFace
  have hnegative (k : ℕ) (hk : 0 < k) : grade (expo (k*H.u) (k*H.v)) < 0 := by
    have hu := Nat.mul_lt_mul_of_pos_left H.endCrossing hk
    simp [grade,expo]; exact_mod_cast hu
  have hmaxGrade : ∀ e ∈ (leadingForm H.rho (-(H.s : ℤ)) H.left.1).support,
      grade e ≤ grade (expo (H.d*H.r) (H.d*H.t)) := by
    intro e he
    have hx := hPmin e he
    have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol H.left.1) (w := wt H.rho (-(H.s : ℤ)))
      (n := vDeg H.rho (-(H.s : ℤ)) H.left.1)
    have hw := hhom (mem_support_iff.mp he)
    have hb := hhom (mem_support_iff.mp hPstart)
    obtain ⟨⟨a,b⟩,rfl⟩ := expo_surjective e
    rw [expo_weight] at hw hb
    simp [expo] at hx
    have hax : ((H.d*H.r : ℕ) : ℤ) ≤ a := by exact_mod_cast hx
    simp only [Prod.fst,Prod.snd] at hw
    have hgradeEq : (H.s : ℤ) *
        (((H.d*H.r : ℕ) : ℤ)-((H.d*H.t : ℕ) : ℤ)-((a : ℤ)-b)) =
        ((H.rho : ℤ)-H.s)*((a : ℤ)-((H.d*H.r : ℕ) : ℤ)) := by
      linear_combination hb-hw
    have hgradeNonneg : 0 ≤ (H.s : ℤ) *
        (((H.d*H.r : ℕ) : ℤ)-((H.d*H.t : ℕ) : ℤ)-((a : ℤ)-b)) := by
      rw [hgradeEq]
      exact mul_nonneg (le_of_lt hsumDir) (sub_nonneg.mpr hax)
    have hgradeBound := nonneg_of_mul_nonneg_right hgradeNonneg hs
    simpa [grade,expo] using (sub_nonneg.mp hgradeBound)
  have hforbid := ggv_cut_corner_proved H.left H.right H.rho (-(H.s : ℤ))
    (H.d*H.r) (H.d*H.t) H.n H.d H.h H.minimal.1 H.direction hρ
    (by omega) H.leftDirection H.rightDirection hpPos hqPos hthreshold hnd1 hnd2
    ⟨_,hPend,hnegative H.d (by omega)⟩ ⟨_,hQend,hnegative H.n (by omega)⟩
    hPstart hmaxGrade hratio H.nProper H.dProper hcop H.hProper
  apply hforbid
  rw [smallDegreeCrossing_cutPoly_maxRootMult P Q H]
  have hρq : (H.rho : ℚ) ≠ 0 := by exact_mod_cast H.rhoPos.ne'
  have hdq : (H.d : ℚ) ≠ 0 := by have := H.dProper; exact_mod_cast (show H.d ≠ 0 by omega)
  have hcornerNat : H.rho*H.r+(H.h-H.t)*H.s+1=H.rho*H.h := by
    have hpositive : 0 < H.rho*H.h := Nat.mul_pos H.rhoPos (by have := H.hProper; omega)
    have := H.cornerEquation; omega
  have hcornerQ : (H.rho : ℚ)*H.r+((H.h : ℚ)-H.t)*H.s+1=(H.rho : ℚ)*H.h := by
    have he : (H.rho : ℚ)*H.r+((H.h-H.t : ℕ) : ℚ)*H.s+1=(H.rho : ℚ)*H.h := by
      exact_mod_cast hcornerNat
    simpa [Nat.cast_sub H.tBound] using he
  constructor
  · push_cast
    field_simp
    nlinarith
  · push_cast
    field_simp

end Dixmier.Weyl
