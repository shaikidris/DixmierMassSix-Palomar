/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVCommonRootOccupiedEndpoints
public import DixmierFormal.Weyl.GGVCompanionJosephFrontier
public import DixmierFormal.Weyl.CompanionPowerCancellation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The actual companion endpoint of a normalized crossing root -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem counterexample_crossing_root_companion_endpoint
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (R : MvPolynomial (Fin 2) ℂ) (ν : ℂ)
    (ρ s m u v r t : ℕ) (w : ℤ)
    (hs : 0 < s) (hm : 0 < m)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hR : R ≠ 0) (hν : ν ≠ 0)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) w)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = C ν * R^m)
    (hu : expo u v ∈ R.support) (hr : expo r t ∈ R.support)
    (hmax : ∀ x ∈ R.support, x 0 ≤ u)
    (htr : t < r) (huv : u < v) :
    ∃ (F : MvPolynomial (Fin 2) ℂ) (f₁ f₂ : ℕ),
      F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ)-s) ∧
      poisson R F = R ∧ expo 1 1 ∈ F.support ∧
      1 < F.support.card ∧ expo f₁ f₂ ∈ F.support ∧
      (∀ x ∈ F.support, x 0 ≤ f₁) ∧
      2 ≤ f₁ ∧ f₁*v=f₂*u ∧
      ρ = (f₂-1)/Nat.gcd (f₁-1) (f₂-1) ∧
      s = (f₁-1)/Nat.gcd (f₁-1) (f₂-1) := by
  classical
  obtain ⟨F₀,hF₀hom,hF₀br⟩ := ggv_preliminary_companion_proved
    P Q hpair ρ (-(s : ℤ)) hdir
  let F := C (m : ℂ)*F₀
  have hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ)-s) := by
    simpa [F,sub_eq_add_neg] using hF₀hom.C_mul (m : ℂ)
  have hbr : poisson R F = R := poisson_power_companion_cancel
    R F₀ ν m hν hm hR (by simpa [hface] using hF₀br)
  have hsρ : s < ρ := by have := hdir.2; omega
  have hbase := homogeneous_companion_base_mem R F ρ s hs hsρ hR hFhom hbr
  have hpos : 0 < grade (expo r t) := by simp [grade,expo]; omega
  have hneg : grade (expo u v) < 0 := by simp [grade,expo]; omega
  have hcard := crossing_poisson_companion_nonmonomial R F (expo r t)
    (expo u v) hbase hbr hr hu hpos hneg
  have hFne : F.support.Nonempty := ⟨expo 1 1,hbase⟩
  obtain ⟨x,hx,hxmax⟩ := Finset.exists_max_image F.support (fun x => x 0) hFne
  obtain ⟨⟨f₁,f₂⟩,rfl⟩ := expo_surjective x
  have hFmax : ∀ x ∈ F.support, x 0 ≤ f₁ := by simpa [expo] using hxmax
  have hf₁ := homogeneous_companion_end_x_ge_two F ρ s f₁ _ hs hdir
    hFhom hbase hFmax hcard
  have hprop := homogeneous_companion_end_proportional R F ρ s u v f₁ f₂
    w _ hs hf₁ hhom hFhom hu hx hmax hFmax hbr
  have hnorm := companion_support_recovers_primitive_direction F ρ s f₁ f₂ _
    hdir hf₁ hFhom hbase hx
  exact ⟨F,f₁,f₂,hFhom,hbr,hbase,hcard,hx,hFmax,hf₁,hprop,hnorm.1,hnorm.2⟩

theorem counterexample_crossing_root_small_degree_coordinates
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (R : MvPolynomial (Fin 2) ℂ) (ν : ℂ)
    (ρ s m u v r t : ℕ) (w : ℤ)
    (hs : 0 < s) (hm : 0 < m)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hR : R ≠ 0) (hν : ν ≠ 0)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) w)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = C ν * R^m)
    (hu : expo u v ∈ R.support) (hr : expo r t ∈ R.support)
    (hmax : ∀ x ∈ R.support, x 0 ≤ u)
    (htr : t < r) (huv : u < v) (hru : r < u) (hsmall : u+v ≤ 15) :
    ∃ (F : MvPolynomial (Fin 2) ℂ) (f₁ f₂ h : ℕ),
      F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ)-s) ∧
      poisson R F = R ∧ expo 1 1 ∈ F.support ∧
      expo f₁ f₂ ∈ F.support ∧ (∀ x ∈ F.support, x 0 ≤ f₁) ∧
      2 ≤ f₁ ∧ f₁*v=f₂*u ∧ Nat.gcd (f₁-1) (f₂-1)=1 ∧
      2 ≤ h ∧ t ≤ h ∧ v=t+ρ*h ∧ ρ*r+(h-t)*s=ρ*h-1 := by
  obtain ⟨F,f₁,f₂,hFhom,hbr,hbase,_,hFend,hFmax,hf₁,hprop,hρnorm,hsnorm⟩ :=
    counterexample_crossing_root_companion_endpoint P Q hpair R ν
      ρ s m u v r t w hs hm hdir hR hν hhom hface hu hr hmax htr huv
  have hcoordinates := homogeneous_small_degree_forbidden_corner
    R F ρ s u v r t f₁ f₂ w ((ρ : ℤ)-s) hhom hFhom hu hr
      hbase hFend huv hsmall hf₁ hprop htr hru hdir
  dsimp at hcoordinates
  rw [← hρnorm, ← hsnorm] at hcoordinates
  obtain ⟨hg,_,h,hh,hth,hv,heq⟩ := hcoordinates
  exact ⟨F,f₁,f₂,h,hFhom,hbr,hbase,hFend,hFmax,hf₁,hprop,hg,hh,hth,hv,heq⟩

end Dixmier.Weyl
