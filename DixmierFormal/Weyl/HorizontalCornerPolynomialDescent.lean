/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalCornerFullRoot
public import DixmierFormal.Weyl.PolynomialLiftFaceTransport
public import DixmierFormal.Weyl.PolynomialConstantCutRecovery

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Polynomial descent from a horizontal normalized corner

A horizontal maximum-root shear is an actual polynomial automorphism.
The exact pair supplies a common strict-negative face after that shear.
The normalized ending corner and reduced weight ratio are retained in
the polynomial Weyl algebra, with no ramified mate left as a premise.
-/

namespace Dixmier.Weyl

private theorem lifted_two_top_orders_InDir
    (T : A1 ℂ) (ρ σ : ℤ) (hpos : 0 < vDeg ρ σ T.1)
    (E B : ℤ × ℕ)
    (hE : E ∈ ramifiedPBWSupport 1 (by omega) (polynomialRamifiedLift 1 T))
    (hB : B ∈ ramifiedPBWSupport 1 (by omega) (polynomialRamifiedLift 1 T))
    (hEt : ramifiedWeight 1 ρ σ E =
      ramifiedWeightDeg 1 (by omega) ρ σ (polynomialRamifiedLift 1 T))
    (hBt : ramifiedWeight 1 ρ σ B =
      ramifiedWeightDeg 1 (by omega) ρ σ (polynomialRamifiedLift 1 T))
    (hord : B.2 < E.2) : InDir ρ σ T.1 := by
  obtain ⟨i,hi,_⟩ :=
    (polynomialRamifiedLift_support_iff_symbol 1 (by omega) T E.1 E.2).mp hE
  obtain ⟨j,hj,_⟩ :=
    (polynomialRamifiedLift_support_iff_symbol 1 (by omega) T B.1 B.2).mp hB
  have hEf : expo i E.2 ∈ (leadingForm ρ σ T.1).support := by
    apply (polynomialRamifiedLift_leading_support_iff 1 (by omega) T ρ σ hpos i E.2).mpr
    simpa only [← hi] using And.intro hE hEt
  have hBf : expo j B.2 ∈ (leadingForm ρ σ T.1).support := by
    apply (polynomialRamifiedLift_leading_support_iff 1 (by omega) T ρ σ hpos j B.2).mpr
    simpa only [← hj] using And.intro hB hBt
  apply Finset.one_lt_card_iff.mpr
  refine ⟨expo i E.2,expo j B.2,hEf,hBf,?_⟩
  intro heq
  have heq₂ := congrArg (fun e : Fin 2 →₀ ℕ => e 1) heq
  exact (Nat.ne_of_gt hord) (by simpa [expo] using heq₂)

theorem horizontal_corner_polynomial_descent
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
    ∃ (c : ℂ) (R S : A1 ℂ) (r s : ℤ),
      IsCounterexamplePair R S ∧ IsDirection r s ∧ 0 < r ∧ s < 0 ∧
      polynomialRamifiedLift 1 R =
        ramifiedCutAut 1 (by omega) 1 0 c (polynomialRamifiedLift 1 P) ∧
      polynomialRamifiedLift 1 S =
        ramifiedCutAut 1 (by omega) 1 0 c (polynomialRamifiedLift 1 Q) ∧
      InDir r s R.1 ∧ InDir r s S.1 ∧
      expo a b ∈ (leadingForm r s R.1).support ∧
      (∀ e ∈ (leadingForm r s R.1).support,
        grade (expo a b) ≤ grade e) ∧
      0 < vDeg r s R.1 ∧ 0 < vDeg r s S.1 ∧
      vDeg r s S.1 * (d : ℤ) = vDeg r s R.1 * (n : ℤ) := by
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair 1 0 hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 0 hdir
  have hPweight : vDeg 1 0 P.1 = (a : ℤ) := by
    have hw := (polynomialFace_point_source_data P 1 0 a b hend).2
    simpa using hw.symm
  have hmax := horizontal_corner_maxRoot_eq_degree P Q hpair hdir hdirP hdirQ
    a b d n h hd hn hh ha hb hend hmin hweight hcop
  have hab : a < b := by
    rw [ha,hb]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hgrade : ((1 : ℤ) / 1) * vDeg 1 0 P.1 -
      (ramifiedCutExponent 1 1 0 + (1 : ℤ)) *
        (maxRootMult (cutPoly 1 0 P.1) : ℤ) < 0 := by
    norm_num [ramifiedCutExponent,hPweight,hmax]
    exact_mod_cast hab
  obtain ⟨c,r,s,hroot,hm,hnew,hr,hs,hEt,hFt,hUpos,hVpos,hratio,
      hEg,hFg,⟨BP,hBP,hBPlow,hBPt⟩,⟨BQ,hBQ,hBQlow,hBQt⟩⟩ :=
    exactPair_maxRoot_cut_exists_common_face_positive_ratio
      1 (by omega) P Q 1 0 hdir (by omega) (by simp) hPpos hQpos
      hdirP hdirQ hpair.1 (by omega) d n (by omega) (by omega) hweight hcop hgrade
  obtain ⟨R,S,hpairNew,hR,hS⟩ := horizontal_cut_recovers_polynomial_counterexample c P Q hpair
  have hRpos := counterexample_vDeg_pos_all_directions R S hpairNew r s hnew
  have hSpos := counterexample_vDeg_pos_all_directions S (-R)
    (isCounterexamplePair_swap_neg R S hpairNew) r s hnew
  have hEpoint := (polynomialRamifiedCut_root_start_on_old_face
    1 (by omega) P 1 0 (by omega) (by simp) (by omega) a b hend c).1.1
  have hEpointQ :
      (vDeg 1 0 Q.1,(cutPoly 1 0 Q.1).rootMultiplicity c) ∈
        ramifiedPBWSupport 1 (by omega)
          (ramifiedCutAut 1 (by omega) 1 0 c (polynomialRamifiedLift 1 Q)) := by
    obtain ⟨e,f,he,_,_⟩ := Finset.one_lt_card_iff.mp hdirQ
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    simpa [ramifiedCutExponent] using (polynomialRamifiedCut_root_start_on_old_face
      1 (by omega) Q 1 0 (by omega) (by simp) (by omega) i j he c).1.1
  simp only [ramifiedCutExponent] at hEt hFt hEpoint hEpointQ
  norm_num [hPweight,hm,hmax] at hEt hEpoint hBPlow
  rw [← hR] at hEt hEpoint hBP hBPt
  rw [← hS] at hFt hEpointQ hBQ hBQt
  have hRF : expo a b ∈ (leadingForm r s R.1).support := by
    apply (polynomialRamifiedLift_leading_support_iff 1 (by omega) R r s hRpos a b).mpr
    simpa using And.intro hEpoint hEt
  have hRdir := lifted_two_top_orders_InDir R r s hRpos ((a : ℤ),b) BP
    hEpoint hBP hEt hBPt hBPlow
  have hSdir : InDir r s S.1 := by
    apply lifted_two_top_orders_InDir S r s hSpos
      (vDeg 1 0 Q.1,(cutPoly 1 0 Q.1).rootMultiplicity c) BQ
    · simpa using hEpointQ
    · exact hBQ
    · simpa using hFt
    · exact hBQt
    · exact hBQlow
  have hupper : ∀ u : ℤ, ∀ j : ℕ,
      (u,j) ∈ ramifiedPBWSupport 1 (by omega) (polynomialRamifiedLift 1 R) → u ≤ a := by
    have hcut := ramifiedCutAut_weight_upper 1 (by omega) 1 0 (a : ℤ)
      (by omega) (by simp) (by omega) c (polynomialRamifiedLift 1 P)
      (by
        intro u j hj
        have ht := polynomialRamifiedLift_weight_le_scaled_vDeg
          1 (by omega) P 1 0 (by simp) u j hj
        simpa [hPweight] using ht)
    rw [← hR] at hcut
    simpa [ramifiedWeight] using hcut
  have hRmin : ∀ e ∈ (leadingForm r s R.1).support,
      grade (expo a b) ≤ grade e := by
    intro e he
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    have ht := (polynomialRamifiedLift_leading_support_iff
      1 (by omega) R r s hRpos i j).mp he
    have hile : (i : ℤ) ≤ a := hupper i j (by simpa using ht.1)
    have hew := ht.2
    have haw := hEt
    norm_num [ramifiedWeight] at hew haw
    have hsj : s < 0 := hs (by omega)
    have hjle : (j : ℤ) ≤ b := by
      by_contra hbad
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) (sub_nonpos.mpr hile)
      have hneg := mul_neg_of_neg_of_pos hsj (show (0 : ℤ) < (j : ℤ) - b by omega)
      nlinarith only [hew,haw,hnonpos,hneg]
    have hnonneg := mul_nonneg (le_of_lt hnew.2) (sub_nonneg.mpr hjle)
    simp [grade,expo]
    nlinarith only [hew,haw,hnonneg,hr]
  rw [← hR,← hS,
    polynomialRamifiedLift_weightDeg_scaled_of_pos 1 (by omega) R r s hRpos,
    polynomialRamifiedLift_weightDeg_scaled_of_pos 1 (by omega) S r s hSpos] at hratio
  norm_num at hratio
  exact ⟨c,R,S,r,s,hpairNew,hnew,hr,hs (by omega),hR,hS,hRdir,hSdir,
    hRF,hRmin,hRpos,hSpos,hratio⟩

end Dixmier.Weyl
