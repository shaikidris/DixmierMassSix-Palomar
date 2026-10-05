/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVNegativeCommonRootNormalization
public import DixmierFormal.Weyl.HomogeneousPowerEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Occupied endpoints inherited by a negative-face common root -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem negative_homogeneous_x_le_of_y_le
    (R : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (w : ℤ)
    (hρ : 0 < ρ) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) w)
    (e f : Fin 2 →₀ ℕ) (he : e ∈ R.support) (hf : f ∈ R.support)
    (hle : e 1 ≤ f 1) : e 0 ≤ f 0 := by
  obtain ⟨⟨a,b⟩,rfl⟩ := expo_surjective e
  obtain ⟨⟨c,d⟩,rfl⟩ := expo_surjective f
  have hew := hhom (mem_support_iff.mp he)
  have hfw := hhom (mem_support_iff.mp hf)
  rw [expo_weight] at hew hfw
  have hbd : (b : ℤ) ≤ d := by exact_mod_cast (show b ≤ d by simpa [expo] using hle)
  have hρz : (0 : ℤ) < ρ := by exact_mod_cast hρ
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have hac : (a : ℤ) ≤ c := by nlinarith
  simpa [expo] using (show a ≤ c by exact_mod_cast hac)

theorem negative_face_power_inherits_occupied_endpoints
    (P : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (ν : ℂ)
    (ρ s m : ℕ) (w : ℤ) (hρ : 0 < ρ) (hs : 0 < s)
    (hR : R ≠ 0) (hν : ν ≠ 0)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) w)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = C ν * R^m)
    (e f : Fin 2 →₀ ℕ)
    (he : e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hf : f ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hemin : ∀ x ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, e 1 ≤ x 1)
    (hfmax : ∀ x ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, x 1 ≤ f 1) :
    ∃ u v r t : ℕ,
      expo u v ∈ R.support ∧ expo r t ∈ R.support ∧
      (∀ x ∈ R.support, x 0 ≤ u) ∧
      (∀ x ∈ R.support, r ≤ x 0) ∧
      e = expo (m*r) (m*t) ∧ f = expo (m*u) (m*v) := by
  classical
  have hne := support_nonempty.mpr hR
  obtain ⟨x,hx,hxmax⟩ := Finset.exists_max_image R.support (fun x => x 0) hne
  obtain ⟨y,hy,hymin⟩ := Finset.exists_min_image R.support (fun x => x 0) hne
  obtain ⟨⟨u,v⟩,rfl⟩ := expo_surjective x
  obtain ⟨⟨r,t⟩,rfl⟩ := expo_surjective y
  have hmax : ∀ x ∈ R.support, x 0 ≤ u := by simpa [expo] using hxmax
  have hmin : ∀ x ∈ R.support, r ≤ x 0 := by simpa [expo] using hymin
  obtain ⟨hup,hrp,hupmax,hrpmin⟩ := leadingFace_power_endpoint_pair
    P R ν ρ s m u v r t w hR hν hs hhom hx hy hmax hmin hface
  have hphom : (leadingForm ρ (-(s : ℤ)) P.1).IsWeightedHomogeneous
      (wt ρ (-(s : ℤ))) (vDeg ρ (-(s : ℤ)) P.1) :=
    weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ (-(s : ℤ))) (n := vDeg ρ (-(s : ℤ)) P.1)
  have hef : e 0 = m*r := by
    apply Nat.le_antisymm
    · simpa [expo] using negative_homogeneous_x_le_of_y_le _ ρ s _ hρ hs
        hphom e _ he hrp (hemin _ hrp)
    · exact hrpmin e he
  have hff : f 0 = m*u := by
    apply Nat.le_antisymm
    · exact hupmax f hf
    · simpa [expo] using negative_homogeneous_x_le_of_y_le _ ρ s _ hρ hs
        hphom _ f hup hf (hfmax _ hup)
  have hfeq : f = expo (m*u) (m*v) := homogeneous_max_x_unique
    _ ρ s (m*u) (m*v) _ hs hphom hup f hf hff
  have heeq : e = expo (m*r) (m*t) := homogeneous_max_x_unique
    _ ρ s (m*r) (m*t) _ hs hphom hrp e he hef
  exact ⟨u,v,r,t,hx,hy,hmax,hmin,heeq,hfeq⟩

theorem negative_face_root_crossing_and_gcd_bound
    (P Q : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (ν : ℂ)
    (ρ s m : ℕ) (w : ℤ) (hρ : 0 < ρ) (hs : 0 < s) (hm : 0 < m)
    (hR : R ≠ 0) (hν : ν ≠ 0)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) w)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = C ν * R^m)
    (hdegree : totalDeg P.1 = m * Nat.gcd (totalDeg P.1) (totalDeg Q.1))
    (e f : Fin 2 →₀ ℕ)
    (he : e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hf : f ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hemin : ∀ x ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, e 1 ≤ x 1)
    (hfmax : ∀ x ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, x 1 ≤ f 1)
    (hepos : 0 < grade e) (hfneg : grade f < 0) :
    ∃ u v r t : ℕ,
      expo u v ∈ R.support ∧ expo r t ∈ R.support ∧
      (∀ x ∈ R.support, x 0 ≤ u) ∧
      (∀ x ∈ R.support, r ≤ x 0) ∧
      t < r ∧ u < v ∧ r < u ∧
      u+v ≤ Nat.gcd (totalDeg P.1) (totalDeg Q.1) ∧
      e = expo (m*r) (m*t) ∧ f = expo (m*u) (m*v) := by
  obtain ⟨u,v,r,t,hu,hr,hmax,hmin,heq,hfq⟩ :=
    negative_face_power_inherits_occupied_endpoints P R ν ρ s m w hρ hs
      hR hν hhom hface e f he hf hemin hfmax
  obtain ⟨htr,huv,hru⟩ := homogeneous_power_crossing_coordinates
    R ρ s m u v r t w hs hhom hu hr hmax (heq ▸ hepos) (hfq ▸ hfneg)
  have hbound := leadingFace_root_endpoint_scaled_totalDeg_le
    P R ν ρ s m u v w hR hν hs hhom hu hmax hface
  have hdegreeBound : u+v ≤ Nat.gcd (totalDeg P.1) (totalDeg Q.1) := by
    rw [hdegree] at hbound
    nlinarith
  exact ⟨u,v,r,t,hu,hr,hmax,hmin,htr,huv,hru,hdegreeBound,heq,hfq⟩

end Dixmier.Weyl
