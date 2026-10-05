/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVNegativeTotalDegreeRatio
public import DixmierFormal.Weyl.GGVGlobalFacePowerRatio
public import DixmierFormal.Weyl.GGVMinimalDegreeNondivisibility

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Common-root exponents normalized by the actual degree gcd -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem nondividing_degrees_coprime_normalization
    (a b : ℕ) (ha : 0 < a) (hab : ¬ a ∣ b) (hba : ¬ b ∣ a) :
    ∃ d n : ℕ, 1 < d ∧ 1 < n ∧ Nat.Coprime d n ∧
      a = d * Nat.gcd a b ∧ b = n * Nat.gcd a b := by
  let g := Nat.gcd a b
  let d := a / g
  let n := b / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have had : d*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hbn : n*g=b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have hd : 1 < d := by
    by_contra h
    have hdle : d ≤ 1 := by omega
    have hdpos : 0 < d := by nlinarith [had]
    have hd1 : d=1 := by omega
    have hag : a=g := by simpa [hd1] using had.symm
    exact hab (hag ▸ Nat.gcd_dvd_right a b)
  have hn : 1 < n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hn0 : n ≠ 0 := by
      intro hz
      have hb0 : b=0 := by simpa [hz] using hbn.symm
      exact hab (hb0 ▸ dvd_zero a)
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn1 : n=1 := by omega
    have hbg : b=g := by simpa [hn1] using hbn.symm
    exact hba (hbg ▸ Nat.gcd_dvd_left a b)
  exact ⟨d,n,hd,hn,Nat.coprime_div_gcd_div_gcd hg,had.symm,hbn.symm⟩

theorem degreeMinimal_subrectangular_negative_common_root
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
    (hentry : (ggvOrderedNegativeFaceSlopes P)[j] = (-(s : ℤ) : ℚ)/ρ)
    (a b u v : ℕ) (ha : 0 < a)
    (hP : IsSubrectangularAt P a b) (hQ : IsSubrectangularAt Q u v)
    (hprop : a*v=b*u) :
    ∃ (d n : ℕ) (R : MvPolynomial (Fin 2) ℂ) (ν μ : ℂ) (w : ℤ),
      1 < d ∧ 1 < n ∧ Nat.Coprime d n ∧
      totalDeg P.1 = d * Nat.gcd (totalDeg P.1) (totalDeg Q.1) ∧
      totalDeg Q.1 = n * Nat.gcd (totalDeg P.1) (totalDeg Q.1) ∧
      R ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ 0 ∧
      IsWeightedHomogeneous (wt (ρ : ℤ) (-(s : ℤ))) R w ∧
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 = (d : ℤ)*w ∧
      leadingForm (ρ : ℤ) (-(s : ℤ)) P.1 = MvPolynomial.C ν * R^d ∧
      leadingForm (ρ : ℤ) (-(s : ℤ)) Q.1 = MvPolynomial.C μ * R^n := by
  have hdegpos : 0 < totalDeg P.1 := by
    rw [subrectangular_totalDeg_eq P a b hP]; omega
  obtain ⟨hab,hba⟩ := degreeMinimal_totalDeg_nondivisibility P Q hmin
  obtain ⟨d,n,hd,hn,hcop,hPd,hQd⟩ :=
    nondividing_degrees_coprime_normalization _ _ hdegpos hab hba
  have hratio := counterexample_subrectangular_negative_total_degree_ratio
    P Q hmin.1 ρ s hρ hdir j hj hentry a b u v ha hP hQ hprop
  have hgpos : 0 < Nat.gcd (totalDeg P.1) (totalDeg Q.1) :=
    Nat.gcd_pos_of_pos_left _ hdegpos
  have hPdZ := congrArg (fun k : ℕ => (k : ℤ)) hPd
  have hQdZ := congrArg (fun k : ℕ => (k : ℤ)) hQd
  push_cast at hPdZ hQdZ
  have hratio' :
      (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (d : ℤ)) *
        (Nat.gcd (totalDeg P.1) (totalDeg Q.1) : ℤ) =
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1 * (n : ℤ)) *
        (Nat.gcd (totalDeg P.1) (totalDeg Q.1) : ℤ) := by
    calc
      _ = vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (totalDeg P.1 : ℤ) := by
        rw [mul_assoc, ← hPdZ]
      _ = vDeg (ρ : ℤ) (-(s : ℤ)) P.1 * (totalDeg Q.1 : ℤ) := hratio
      _ = _ := by rw [mul_assoc, ← hQdZ]
  have hcancel : vDeg (ρ : ℤ) (-(s : ℤ)) Q.1 * (d : ℤ) =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 * (n : ℤ) := by
    apply mul_right_cancel₀ (by exact_mod_cast (ne_of_gt hgpos) :
      (Nat.gcd (totalDeg P.1) (totalDeg Q.1) : ℤ) ≠ 0)
    exact hratio'
  have hp := counterexample_vDeg_pos_all_directions P Q hmin.1 _ _ hdir
  have hq := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hmin.1) _ _ hdir
  have hnat : (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1).toNat*d =
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1).toNat*n := by
    rw [← Int.toNat_of_nonneg hp.le, ← Int.toNat_of_nonneg hq.le] at hcancel
    exact_mod_cast hcancel
  obtain ⟨R,ν,μ,w,hR,hν,hμ,hw,hweight,hfaceP,hfaceQ⟩ :=
    counterexample_leading_faces_homogeneous_common_root P Q hmin.1 _ _ hdir
      n d (by omega) (by omega) hcop hnat
  exact ⟨d,n,R,ν,μ,w,hd,hn,hcop,hPd,hQd,hR,hν,hμ,hw,hweight,hfaceP,hfaceQ⟩

end Dixmier.Weyl
