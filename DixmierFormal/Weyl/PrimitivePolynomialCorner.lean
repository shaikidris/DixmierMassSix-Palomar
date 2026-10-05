/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HomogeneousPowerEndpoint
public import DixmierFormal.Weyl.PoissonDiagonalStart

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Primitive endpoints exclude polynomial normalized corners

A positive-weight homogeneous root with endpoint `(u,u+1)` cannot admit
an exact polynomial Poisson companion. Its positive-grade start forces a
nonprimitive endpoint by the companion endpoint theorem.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem homogeneous_unit_defect_endpoint_impossible
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s u : ℕ) (q : ℤ)
    (hs : 0 < s) (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hq : 0 < q)
    (hRhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) q)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hend : expo u (u+1) ∈ R.support)
    (hmax : ∀ e ∈ R.support, e 0 ≤ u)
    (hcard : 1 < R.support.card) (hcomp : poisson R F = R) : False := by
  classical
  have hRne : R ≠ 0 := support_nonempty.mp ⟨_,hend⟩
  obtain ⟨e,he,hmin⟩ := Finset.exists_min_image R.support (fun e => e 0)
    (support_nonempty.mpr hRne)
  obtain ⟨⟨r,t⟩,rfl⟩ := expo_surjective e
  have hmin' : ∀ e ∈ R.support, r ≤ e 0 := by simpa [expo] using hmin
  have hru : r < u := by
    have hle : r ≤ u := by simpa [expo] using hmax _ he
    by_contra hn
    have heq : r = u := by omega
    have hsub : R.support ⊆ {expo u (u+1)} := by
      intro e he'
      have hx : e 0 = u := by have := hmin' e he'; have := hmax e he'; omega
      exact Finset.mem_singleton.mpr
        (homogeneous_max_x_unique R ρ s u (u+1) q hs hRhom hend e he' hx)
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  have hsρ : (s : ℤ) < ρ := by have := hdir.2; omega
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have hwEnd := hRhom (mem_support_iff.mp hend)
  have hwStart := hRhom (mem_support_iff.mp he)
  rw [expo_weight] at hwEnd hwStart
  have hstart : 0 ≤ (r : ℤ) - t := by
    have hruz : (r : ℤ) < u := by exact_mod_cast hru
    have hprod : 0 < ((ρ : ℤ) - s) * ((u : ℤ) - r) := mul_pos (by omega) (by omega)
    have hline : (s : ℤ) * ((r : ℤ) - t + 1) =
        ((ρ : ℤ) - s) * ((u : ℤ) - r) := by
      push_cast at hwEnd
      nlinarith only [hwEnd,hwStart]
    have : 0 < (r : ℤ) - t + 1 := (mul_pos_iff_of_pos_left hsz).mp (hline ▸ hprod)
    omega
  have hgradeMax : ∀ e ∈ R.support,
      Finsupp.weight (wt 1 (-1)) e ≤ Finsupp.weight (wt 1 (-1)) (expo r t) := by
    intro e he'
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    have hw := hRhom (mem_support_iff.mp he')
    rw [expo_weight] at hw
    have hx : r ≤ i := by simpa [expo] using hmin' _ he'
    have hxz : (r : ℤ) ≤ i := by exact_mod_cast hx
    have hprod : 0 ≤ ((ρ : ℤ) - s) * ((i : ℤ) - r) := mul_nonneg (by omega) (by omega)
    rw [expo_weight,expo_weight]
    nlinarith only [hw,hwStart,hprod,hsz]
  have hstartPos : 0 < grade (expo r t) := by
    simp [grade,expo]
    by_contra hn
    have hrt : r = t := by omega
    have hrpos : 0 < r := by
      subst t
      by_contra hn'
      have hrzero : r = 0 := by omega
      simp [hrzero] at hwStart
      omega
    exact poisson_companion_no_diagonal_homogeneous_max
      ρ (-(s : ℤ)) q ((ρ : ℤ)-s) (by have := hdir.2; omega)
      R F hRhom hFhom hcomp he hgradeMax
      (by simpa [expo] using hrt) (by simpa [expo] using hrpos)
  have hFne : F ≠ 0 := by
    intro hz
    rw [hz] at hcomp
    simp [poisson] at hcomp
    exact hRne hcomp.symm
  obtain ⟨eF,heF,hFmax⟩ := Finset.exists_max_image F.support (fun e => e 0)
    (support_nonempty.mpr hFne)
  obtain ⟨⟨f₁,f₂⟩,rfl⟩ := expo_surjective eF
  have hbad := (homogeneous_companion_end_nonprimitive R F ρ s u (u+1)
    r t f₁ f₂ q hs hdir hRhom hFhom hend he hmax heF
    (by simpa [expo] using hFmax) hcomp hstartPos (by simp [grade,expo])).2.2
  simpa [Nat.gcd_add_self_right] using hbad

end Dixmier.Weyl
