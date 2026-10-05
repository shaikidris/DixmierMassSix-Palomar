module

public import DixmierFormal.Weyl.FiniteCutCornerDescent
public import DixmierFormal.Weyl.RamifiedMinimumGradeEnding
public import DixmierFormal.Weyl.CutCornerNormalization

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The polynomial-source ramified cut-corner exclusion

The normalized maximum-root cut supplies the first actual corner state.
Finite admissible cut histories preserve the original exact polynomial
source, so the finite-direction descent excludes that state.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ggv_cut_corner_proved
    (P Q : A1 ℂ) (ρ σ : ℤ) (u v n d h : ℕ)
    (hpair : IsCounterexamplePair P Q) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hPpos : 0 < vDeg ρ σ P.1) (hQpos : 0 < vDeg ρ σ Q.1)
    (hsum : ρ+σ < vDeg ρ σ P.1+vDeg ρ σ Q.1)
    (hnd₁ : ¬(vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1))
    (hnd₂ : ¬(vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1))
    (hnegP : ∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0)
    (hnegQ : ∃ e ∈ (leadingForm ρ σ Q.1).support, grade e < 0)
    (hpoint : expo u v ∈ (leadingForm ρ σ P.1).support)
    (hmax : ∀ e ∈ (leadingForm ρ σ P.1).support, grade e ≤ grade (expo u v))
    (hratio : vDeg ρ σ Q.1*(d:ℤ)=vDeg ρ σ P.1*(n:ℤ))
    (hn : 1 < n) (hd : 1 < d) (hcop : Nat.Coprime n d) (hh : 2 ≤ h) :
    ¬ (((u:ℚ)+((v:ℚ)-maxRootMult (cutPoly ρ σ P.1))*σ/ρ)/d=h-1/ρ ∧
      (maxRootMult (cutPoly ρ σ P.1):ℚ)/d=h) := by
  intro hcorner
  let l := ρ.toNat
  have hl : 0 < l := by dsimp [l]; omega
  have hρl : (l:ℤ)=ρ := Int.toNat_of_nonneg (le_of_lt hρ)
  have hdiv : ρ ∣ (l:ℤ) := by rw [hρl]
  obtain ⟨c,r,s,_,_,hnewdir,hr,hs,hEpoint,hFpoint,hEtop,hFtop,hUpos,hVpos,
      hnewratio,_,_,hthreshold,hcomm,_,_,hEmin,hFmin,hBP,_⟩ :=
    counterexample_normalized_cut_corner_configuration
      l hl P Q hpair ρ σ hdir hρ hσ hρl hdirP hdirQ hsum u v d n h
      hd hn hh hratio hcop hnegP hpoint hcorner
  let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
  let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
  let E : ℤ × ℕ := ((d:ℤ)*((h:ℤ)*(l:ℤ)-1),d*h)
  let F : ℤ × ℕ := (((l:ℤ)/ρ)*vDeg ρ σ Q.1-
    ramifiedCutExponent l ρ σ*( (cutPoly ρ σ Q.1).rootMultiplicity c:ℤ),
    (cutPoly ρ σ Q.1).rootMultiplicity c)
  have hU : U ≠ 0 := by
    intro hz; change V*U-U*V=1 at hcomm
    rw [hz] at hcomm; norm_num at hcomm
  have hV : V ≠ 0 := by
    intro hz; change V*U-U*V=1 at hcomm
    rw [hz] at hcomm; norm_num at hcomm
  have hPend := ramified_min_grade_top_canonical_ending
    l hl r s hr hnewdir.2 U E hEpoint hEtop hEmin
  have hQend := ramified_min_grade_top_canonical_ending
    l hl r s hr hnewdir.2 V F hFpoint hFtop hFmin
  have ht : 0 < ramifiedWeightDeg l hl r s U+
      ramifiedWeightDeg l hl r s V-(l:ℤ)*(r+s) := sub_pos.mpr hthreshold
  have hprop := ramified_exact_pair_canonical_ends_proportional
    l hl r s hr hnewdir.2 U V hU hV hcomm hUpos hVpos ht n d hnewratio
  have hx : (n:ℤ)*E.1=(d:ℤ)*F.1 := by
    simpa only [hPend.1,hQend.1,hPend.2,hQend.2] using hprop.1
  have hy : n*E.2=d*F.2 := by
    simpa only [hPend.1,hQend.1] using hprop.2
  have hmate := ramified_normalized_corner_proportion_mate_coordinates
    l d n h (by omega) E.1 F.1 E.2 F.2 hx hy
    (by dsimp [E]; ring) rfl
  let a : AdmissibleRamifiedCut l := ⟨ρ,σ,c,hρ,hdiv,hσ,hdir.2⟩
  have hnextU : finiteCutImage l hl [a] P=U := rfl
  have hnextV : finiteCutImage l hl [a] Q=V := rfl
  obtain ⟨B,hB,hBlower,hBtop⟩ := hBP
  obtain ⟨hBorder,_,hBweight⟩ := ramified_face_point_topLaurent_at_order
    l hl r s hr U B hB hBtop
    (by intro p hp; exact ramifiedWeight_le_weightDeg_of_mem l hl r s U p hp)
  have hBpoly := (ramifiedTopFacePolynomial_mem_support_iff l hl r s U B.2).mpr
    ⟨hBorder,hBweight⟩
  have H : FiniteCutCornerState l hl P Q n d h [a] r s := by
    refine ⟨hnewdir,hr,le_of_lt hs,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [hnextU] using hUpos
    · simpa only [hnextV] using hVpos
    · simpa only [hnextU,hnextV] using hnewratio
    · simpa only [hnextU,E,Prod.snd] using hPend.1
    · simpa only [hnextV,hmate.2] using hQend.1
    · rw [hnextU]
      simpa only [E,Prod.fst,Prod.snd,mul_comm (h:ℤ) (l:ℤ)] using hPend.2
    · rw [hnextV,← hmate.2]
      exact hQend.2.trans hmate.1
    · refine ⟨B.2,?_,?_⟩
      · simpa only [hnextU] using hBpoly
      · rw [hnextU,hPend.1]
        change B.2 ≠ d*h
        omega
  exact finiteCutCornerState_impossible l hl P Q hpair.1 n d h
    (by omega) (by omega) hh hcop.symm [a] r s H

end Dixmier.Weyl
