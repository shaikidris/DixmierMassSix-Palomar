/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVMinimalCrossingPair
public import DixmierFormal.Weyl.GGVOrderedGlobalRatio
public import DixmierFormal.Weyl.GGVPairedHorizontalBoundary

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Negative-face ratios equal the total-degree ratio of a standard pair

The constant ratio on the finite ordered negative-face list reaches the
horizontal boundary. Proportional occupied rectangles identify that
boundary ratio with the ratio of the two actual total degrees.
-/
namespace Dixmier.Weyl
set_option maxHeartbeats 1000000

theorem counterexample_ordered_ratio_eq_horizontal
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (i : ℕ) (hi : i < (ggvOrderedNegativeFaceSlopes P).length) :
    ggvNegativeFacePairRatio P Q (ggvOrderedNegativeFaceSlopes P)[i] =
      (vDeg 1 0 Q.1 : ℚ)/(vDeg 1 0 P.1 : ℚ) := by
  let L := ggvOrderedNegativeFaceSlopes P
  let j := L.length-1
  have hj : j < L.length := by dsimp [j,L]; omega
  have hjlast : j+1=L.length := by dsimp [j,L]; omega
  let t := L[j]
  obtain ⟨ρ,s,hρ,hs,hdir,hface,hentry,hρeq,hσeq⟩ :=
    ggv_ordered_negative_entry_nat_face P t (List.getElem_mem hj)
  obtain ⟨n,d,_,hd,_,hN,hH⟩ :=
    counterexample_last_negative_horizontal_common_weight_ratio
      P Q hpair ρ s hρ hs hdir j hjlast hentry hface
  have hpN := counterexample_vDeg_pos_all_directions P Q hpair
    (ρ : ℤ) (-(s : ℤ)) hdir
  have hpH := counterexample_vDeg_pos_all_directions P Q hpair 1 0
    (by norm_num [IsDirection])
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hpNQ : (vDeg (ρ : ℤ) (-(s : ℤ)) P.1 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpN)
  have hpHQ : (vDeg 1 0 P.1 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpH)
  have hNQ : (vDeg (ρ : ℤ) (-(s : ℤ)) P.1 : ℚ)*n =
      (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 : ℚ)*d := by exact_mod_cast hN
  have hHQ : (vDeg 1 0 P.1 : ℚ)*n = (vDeg 1 0 Q.1 : ℚ)*d := by
    exact_mod_cast hH
  have hlast : ggvNegativeFacePairRatio P Q t = (n : ℚ)/d := by
    unfold ggvNegativeFacePairRatio
    rw [← hρeq,← hσeq]
    exact (div_eq_div_iff hpNQ hdQ).mpr (by simpa [mul_comm] using hNQ.symm)
  have hhorizontal : (vDeg 1 0 Q.1 : ℚ)/(vDeg 1 0 P.1 : ℚ) = (n : ℚ)/d :=
    (div_eq_div_iff hpHQ hdQ).mpr (by simpa [mul_comm] using hHQ.symm)
  have hfirst := counterexample_ordered_ratio_eq_first P Q hpair i hi
  have hlastfirst := counterexample_ordered_ratio_eq_first P Q hpair j hj
  exact (hfirst.trans hlastfirst.symm).trans (hlast.trans hhorizontal.symm)

theorem counterexample_native_negative_ratio_eq_horizontal
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] = (-(s : ℤ) : ℚ)/ρ) :
    (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 : ℚ)/
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1 : ℚ) =
      (vDeg 1 0 Q.1 : ℚ)/(vDeg 1 0 P.1 : ℚ) := by
  let t := (ggvOrderedNegativeFaceSlopes P)[j]
  obtain ⟨ρ₀,s₀,hρ₀,_,hdir₀,_,hentry₀,hρeq₀,hσeq₀⟩ :=
    ggv_ordered_negative_entry_nat_face P t (List.getElem_mem hj)
  obtain ⟨hρsame,hσsame⟩ := ggv_primitive_negative_normal_unique
    (ρ : ℤ) (-(s : ℤ)) (ρ₀ : ℤ) (-(s₀ : ℤ)) hdir hdir₀
    (by exact_mod_cast hρ) (by exact_mod_cast hρ₀) (hentry.symm.trans hentry₀)
  have hρeq : (ρ : ℤ) = (t.den : ℤ) := hρsame.trans hρeq₀
  have hσeq : -(s : ℤ) = t.num := hσsame.trans hσeq₀
  have hh := counterexample_ordered_ratio_eq_horizontal P Q hpair j hj
  change ggvNegativeFacePairRatio P Q t = _ at hh
  simpa only [ggvNegativeFacePairRatio,← hρeq,← hσeq] using hh

theorem counterexample_subrectangular_negative_total_degree_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] = (-(s : ℤ) : ℚ)/ρ)
    (a b u v : ℕ) (ha : 0 < a)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v)
    (hprop : a*v=b*u) :
    vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (totalDeg P.1 : ℤ) =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 * (totalDeg Q.1 : ℤ) := by
  have hh := counterexample_native_negative_ratio_eq_horizontal
    P Q hpair ρ s hρ hdir j hj hentry
  rw [(subrectangular_horizontal_weight_and_cut_degree P a b hP).1,
    (subrectangular_horizontal_weight_and_cut_degree Q u v hQ).1] at hh
  have hp := counterexample_vDeg_pos_all_directions P Q hpair
    (ρ : ℤ) (-(s : ℤ)) hdir
  have hpQ : (vDeg (ρ : ℤ) (-(s : ℤ)) P.1 : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp)
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hz : vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (a : ℤ) =
      (u : ℤ)*vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    exact_mod_cast (div_eq_div_iff hpQ haQ).mp hh
  have hpropZ : (a : ℤ)*v=(b : ℤ)*u := by exact_mod_cast hprop
  have hmul := congrArg (fun x : ℤ => x*((a : ℤ)+b)) hz
  have hpropScaled := congrArg
    (fun x : ℤ => vDeg (ρ : ℤ) (-(s : ℤ)) P.1*x) hpropZ
  have hcancel : (a : ℤ)*
      (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1*((a : ℤ)+b)-
        vDeg (ρ : ℤ) (-(s : ℤ)) P.1*((u : ℤ)+v))=0 := by
    linear_combination hmul-hpropScaled
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left
    (by exact_mod_cast (ne_of_gt ha) : (a : ℤ) ≠ 0))
  simpa only [subrectangular_totalDeg_eq P a b hP,
    subrectangular_totalDeg_eq Q u v hQ,Nat.cast_add] using heq

end Dixmier.Weyl
