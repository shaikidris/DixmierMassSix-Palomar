/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerRootOrderRatio
public import DixmierFormal.Weyl.GGVPolynomialCompanionCutLift
public import DixmierFormal.Weyl.GGVCompanionJosephFrontier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Full root multiplicity at a horizontal normalized corner

The polynomial companion forces the selected cut grade to be negative.
The exact Weyl relation makes its maximum root order divisible by the
reduced weight denominator. At a normalized horizontal corner these two
facts force that root to consume the whole face degree, at every height.
-/

namespace Dixmier.Weyl

open Polynomial

theorem horizontal_corner_maxRoot_eq_degree
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection 1 0)
    (hdirP : InDir 1 0 P.1) (hdirQ : InDir 1 0 Q.1)
    (a b d n h : ℕ) (hd : 1 < d) (_hn : 1 < n) (hh : 2 ≤ h)
    (ha : a = d * (h - 1)) (hb : b = d * h)
    (hend : expo a b ∈ (leadingForm 1 0 P.1).support)
    (hmin : ∀ e ∈ (leadingForm 1 0 P.1).support,
      grade (expo a b) ≤ grade e)
    (hweight : vDeg 1 0 Q.1 * (d : ℤ) =
      vDeg 1 0 P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d) :
    maxRootMult (cutPoly 1 0 P.1) = b := by
  have hP := counterexample_vDeg_pos_all_directions P Q hpair 1 0 hdir
  have hQ := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 0 hdir
  have hdeg := cutPoly_natDegree_of_min_grade_endpoint P 1 0 a b
    (by omega) (by omega) hend hmin
  have hbpos : 0 < b := by rw [hb]; positivity
  have hPweight : vDeg 1 0 P.1 = (a : ℤ) := by
    have hw := (polynomialFace_point_source_data P 1 0 a b hend).2
    simpa using hw.symm
  have hsum : 1 < vDeg 1 0 P.1 + vDeg 1 0 Q.1 := by omega
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,_,_,_⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      1 (by omega) P Q 1 0 hdir (by omega) (by simp)
      hP hQ hdirP hdirQ hpair.1 (by simpa using hsum)
  have hratioZ := congrArg (fun k : ℕ => (k : ℤ)) hratio
  push_cast at hratioZ
  rw [Int.toNat_of_nonneg (le_of_lt hP),
    Int.toNat_of_nonneg (le_of_lt hQ)] at hratioZ
  have hdiv : d ∣ maxRootMult (cutPoly 1 0 P.1) :=
    (reduced_ratio_root_orders_divide
      (vDeg 1 0 P.1) (vDeg 1 0 Q.1) d n
      (maxRootMult (cutPoly 1 0 P.1))
      ((cutPoly 1 0 Q.1).rootMultiplicity c)
      hP hweight hratioZ hcop).1
  have hneg := preliminary_companion_maxRoot_cut_grade_negative
    ggv_preliminary_companion_proved 1 (by omega) P Q hpair 1 0 hdir
      (by omega) (by simp) hdirP (by omega : 0 < (cutPoly 1 0 P.1).natDegree)
      (by
        norm_num [ramifiedCutExponent, hPweight, hdeg]
        have hab : a < b := by
          rw [ha,hb]
          exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        have habZ : (a : ℤ) < (b : ℤ) := by exact_mod_cast hab
        omega)
  norm_num [ramifiedCutExponent, hPweight] at hneg
  have hpne : cutPoly 1 0 P.1 ≠ 0 :=
    ne_zero_of_natDegree_gt (by rw [hdeg]; exact hbpos)
  have hupper := maxRootMult_le_natDegree (cutPoly 1 0 P.1) hpne
  rw [hdeg] at hupper
  obtain ⟨k,hk⟩ := hdiv
  have hlow : a < maxRootMult (cutPoly 1 0 P.1) := by exact_mod_cast hneg
  have hkh : h ≤ k := by
    rw [ha,hk] at hlow
    have hpred := lt_of_mul_lt_mul_left hlow (Nat.zero_le d)
    omega
  rw [hk,hb] at hupper ⊢
  have hkh' := le_of_mul_le_mul_left hupper (by omega : 0 < d)
  rw [show k = h by omega]

/-- The horizontal corner face polynomial is a single linear power.
This is a root classification, not the descending-direction exclusion. -/
theorem horizontal_corner_cutPoly_linear_power
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection 1 0)
    (hdirP : InDir 1 0 P.1) (hdirQ : InDir 1 0 Q.1)
    (a b d n h : ℕ) (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : a = d * (h - 1)) (hb : b = d * h)
    (hend : expo a b ∈ (leadingForm 1 0 P.1).support)
    (hmin : ∀ e ∈ (leadingForm 1 0 P.1).support,
      grade (expo a b) ≤ grade e)
    (hweight : vDeg 1 0 Q.1 * (d : ℤ) =
      vDeg 1 0 P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d) :
    ∃ c : ℂ, (cutPoly 1 0 P.1).IsRoot c ∧
      cutPoly 1 0 P.1 = C (cutPoly 1 0 P.1).leadingCoeff * (X - C c) ^ b := by
  have hdeg := cutPoly_natDegree_of_min_grade_endpoint P 1 0 a b
    (by omega) (by omega) hend hmin
  have hmax := horizontal_corner_maxRoot_eq_degree P Q hpair hdir hdirP hdirQ
    a b d n h hd hn hh ha hb hend hmin hweight hcop
  have hbpos : 0 < b := by rw [hb]; positivity
  obtain ⟨c,hroot,hpower⟩ := polynomial_eq_linear_power_of_maxRootMult_eq_natDegree
    (cutPoly 1 0 P.1) (by omega) (hmax.trans hdeg.symm)
  exact ⟨c,hroot,by simpa only [hdeg] using hpower⟩

end Dixmier.Weyl
