/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PrimitivePolynomialCorner
public import DixmierFormal.Weyl.GGVStrictNegativeCornerFrontier
public import DixmierFormal.Weyl.GGVGlobalFacePowerRatio
public import DixmierFormal.Weyl.CompanionPowerCancellation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Polynomial forbidden corners for actual Weyl counterexample pairs -/

namespace Dixmier.Weyl

open MvPolynomial

theorem counterexample_strict_negative_unit_corner_impossible
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s a b n d h : ℕ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hdirP : InDir ρ (-(s : ℤ)) P.1)
    (hP : 0 < vDeg ρ (-(s : ℤ)) P.1)
    (hQ : 0 < vDeg ρ (-(s : ℤ)) Q.1)
    (hend : expo a b ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hminGrade : ∀ e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support,
      grade (expo a b) ≤ grade e)
    (hratio : vDeg ρ (-(s : ℤ)) Q.1 * d = vDeg ρ (-(s : ℤ)) P.1 * n)
    (hn : 1 < n) (hd : 1 < d) (hcop : Nat.Coprime n d) (hh : 2 ≤ h)
    (ha : a = d * (h-1)) (hb : b = d*h) : False := by
  classical
  have hratioNat : (vDeg ρ (-(s : ℤ)) Q.1).toNat * d =
      (vDeg ρ (-(s : ℤ)) P.1).toNat * n := by
    have hcastP : ((vDeg ρ (-(s : ℤ)) P.1).toNat : ℤ) = vDeg ρ (-(s : ℤ)) P.1 := by omega
    have hcastQ : ((vDeg ρ (-(s : ℤ)) Q.1).toNat : ℤ) = vDeg ρ (-(s : ℤ)) Q.1 := by omega
    have heq : ((vDeg ρ (-(s : ℤ)) Q.1).toNat : ℤ) * (d : ℤ) =
        ((vDeg ρ (-(s : ℤ)) P.1).toNat : ℤ) * (n : ℤ) := by
      simpa only [hcastP,hcastQ] using hratio
    exact_mod_cast heq
  obtain ⟨R,ν,μ,q,hRne,hν,hμ,hRhom,hweight,hPface,hQface⟩ :=
    counterexample_leading_faces_homogeneous_common_root P Q hpair ρ (-(s : ℤ))
      hdir n d (by omega) (by omega) hcop.symm hratioNat
  have hq : 0 < q := by
    have hdz : (0 : ℤ) < d := by exact_mod_cast (show 0 < d by omega)
    nlinarith only [hP,hweight,hdz]
  obtain ⟨F₀,hF₀hom,hF₀br⟩ := ggv_preliminary_companion_proved P Q hpair ρ (-(s : ℤ)) hdir
  let F := C (d : ℂ) * F₀
  have hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ)-s) := by
    simpa [F,sub_eq_add_neg] using hF₀hom.C_mul (d : ℂ)
  have hcomp : poisson R F = R := poisson_power_companion_cancel R F₀ ν d hν
    (by omega) hRne (by simpa [hPface] using hF₀br)
  obtain ⟨eMax,heMax,hmax⟩ := Finset.exists_max_image R.support (fun e => e 0)
    (support_nonempty.mpr hRne)
  obtain ⟨eMin,heMin,hmin⟩ := Finset.exists_min_image R.support (fun e => e 0)
    (support_nonempty.mpr hRne)
  obtain ⟨⟨u,v⟩,rfl⟩ := expo_surjective eMax
  obtain ⟨⟨r,t⟩,rfl⟩ := expo_surjective eMin
  have hmax' : ∀ e ∈ R.support, e 0 ≤ u := by simpa [expo] using hmax
  have hmin' : ∀ e ∈ R.support, r ≤ e 0 := by simpa [expo] using hmin
  have hpower := leadingFace_power_endpoint_pair P R ν ρ s d u v r t q
    hRne hν hs hRhom heMax heMin hmax' hmin' hPface
  have hPhom : (leadingForm ρ (-(s : ℤ)) P.1).IsWeightedHomogeneous
      (wt ρ (-(s : ℤ))) (vDeg ρ (-(s : ℤ)) P.1) :=
    weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ (-(s : ℤ))) (n := vDeg ρ (-(s : ℤ)) P.1)
  have hsρ : (s : ℤ) < ρ := by have := hdir.2; omega
  have hmaxP : ∀ e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, e 0 ≤ a := by
    intro e he
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    have hw := hPhom (mem_support_iff.mp he)
    have hwEnd := hPhom (mem_support_iff.mp hend)
    rw [expo_weight] at hw hwEnd
    have hg : (a : ℤ)-b ≤ (i : ℤ)-j := by simpa [grade,expo] using hminGrade _ he
    have hsz : (0 : ℤ) < s := by exact_mod_cast hs
    have hprod : 0 ≤ (s : ℤ)*(((i : ℤ)-j)-((a : ℤ)-b)) := mul_nonneg (by omega) (by omega)
    have : (i : ℤ) ≤ a := by nlinarith only [hw,hwEnd,hprod,hsρ]
    simpa [expo] using (show i ≤ a by exact_mod_cast this)
  have ha' : a = d*u := by
    have h₁ : d*u ≤ a := by simpa [expo] using hmaxP _ hpower.1
    have h₂ : a ≤ d*u := by simpa [expo] using hpower.2.2.1 _ hend
    omega
  have hb' : b = d*v := by
    have hw := hPhom (mem_support_iff.mp hend)
    have hw' := hPhom (mem_support_iff.mp hpower.1)
    rw [expo_weight,ha'] at hw
    rw [expo_weight] at hw'
    have hsz : (0 : ℤ) < s := by exact_mod_cast hs
    have heq : (b : ℤ) = (d*v : ℕ) := by nlinarith only [hw,hw',hsz]
    exact_mod_cast heq
  have hu : u = h-1 := mul_left_cancel₀ (by omega : d ≠ 0) (ha'.symm.trans ha)
  have hv : v = h := mul_left_cancel₀ (by omega : d ≠ 0) (hb'.symm.trans hb)
  have hvu : v = u+1 := by omega
  have hcard : 1 < R.support.card := by
    by_contra hn'
    have hsub : R.support ⊆ {expo u v} := by
      intro e he
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp (by omega)) e he _ heMax)
    have hmono := eq_monomial_of_support_subset_singleton
      (fun e he => Finset.mem_singleton.mp (hsub he))
    have hle : (leadingForm ρ (-(s : ℤ)) P.1).support.card ≤ 1 := by
      rw [hPface,hmono,monomial_pow,C_mul_monomial]
      simp only [support_monomial]
      split_ifs <;> simp
    exact (not_le_of_gt hdirP) hle
  exact homogeneous_unit_defect_endpoint_impossible R F ρ s u q hs hdir hq
    hRhom hFhom (by simpa [hvu] using heMax) hmax' hcard hcomp

theorem ggv_strict_negative_corner_proved : GGVStrictNegativeCornerInput := by
  intro P Q ρ σ a b n d h hpair hdir hσ hdirP _hdirQ hP hQ _hnd₁ _hnd₂
    hend hmin hratio hn hd hcop hh hcorner
  have hρpos : 0 < ρ := by have := hdir.2; omega
  let r := ρ.toNat
  let s := (-σ).toNat
  have hr : (r : ℤ) = ρ := by omega
  have hs : -(s : ℤ) = σ := by omega
  have hspos : 0 < s := by omega
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have haQ := (div_eq_iff hdQ).mp hcorner.1
  have hbQ := (div_eq_iff hdQ).mp hcorner.2
  have ha : a = d*(h-1) := by
    have hcast : ((h-1 : ℕ) : ℚ) = (h : ℚ)-1 := by
      rw [Nat.cast_sub (show 1 ≤ h by omega),Nat.cast_one]
    have heq : (a : ℚ) = (d : ℚ)*((h-1 : ℕ) : ℚ) := by
      rw [hcast]
      nlinarith only [haQ]
    exact_mod_cast heq
  have hb : b = d*h := by
    exact_mod_cast (by nlinarith only [hbQ] : (b : ℚ) = (d : ℚ)*(h : ℚ))
  exact counterexample_strict_negative_unit_corner_impossible P Q hpair r s a b n d h
    hspos (by simpa [hr,hs] using hdir) (by simpa [hr,hs] using hdirP)
    (by simpa [hr,hs] using hP) (by simpa [hr,hs] using hQ)
    (by simpa [hr,hs] using hend) (by simpa [hr,hs] using hmin)
    (by simpa [hr,hs] using hratio) hn hd hcop hh ha hb

/-- The literal polynomial forbidden-corner contract, including its horizontal sector. -/
theorem ggv_polynomial_corner_proved :
    ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ), IsCounterexamplePair P Q →
      IsDirection ρ σ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
      0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 →
      ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
      expo a b ∈ (leadingForm ρ σ P.1).support →
      (∀ e ∈ (leadingForm ρ σ P.1).support, grade (expo a b) ≤ grade e) →
      vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
      ¬ ((a : ℚ) / d = h - 1 ∧ (b : ℚ) / d = h) :=
  ggv_polynomial_corner_of_strict_negative ggv_strict_negative_corner_proved

end Dixmier.Weyl
