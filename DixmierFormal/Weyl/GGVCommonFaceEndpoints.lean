/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVGlobalFacePowerRatio
public import DixmierFormal.Weyl.HomogeneousPowerEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Proportional endpoints of actual common-power faces

On a strict negative direction, the shared homogeneous root has minimum
and maximum `x`-coordinates. Both actual leading faces inherit those two
endpoints, scaled by their respective reduced outer exponents. This is the
operator-level endpoint proportionality used along G13's direction chain.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- For any strict negative common-power face, both actual operators have
the corresponding occupied extreme endpoints. Their coordinates have the
same root and hence the same reduced proportionality. -/
theorem counterexample_common_face_proportional_endpoints
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hratio : (vDeg (ρ : ℤ) (-(s : ℤ)) Q.1).toNat * d =
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1).toNat * n) :
    ∃ u v r t : ℕ,
      expo (d * u) (d * v) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      expo (n * u) (n * v) ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support ∧
      expo (d * r) (d * t) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      expo (n * r) (n * t) ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support ∧
      (∀ e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, d * r ≤ e 0 ∧ e 0 ≤ d * u) ∧
      (∀ e ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support, n * r ≤ e 0 ∧ e 0 ≤ n * u) := by
  classical
  obtain ⟨S, ν, μ, degree, hS, hν, hμ, hhom, _, hPface, hQface⟩ :=
    counterexample_leading_faces_homogeneous_common_root
      P Q hpair ρ (-(s : ℤ)) hdir n d hn hd hcop hratio
  have hsupport : S.support.Nonempty := MvPolynomial.support_nonempty.mpr hS
  obtain ⟨eMax, heMax, hmax⟩ :=
    Finset.exists_max_image S.support (fun e => e 0) hsupport
  obtain ⟨eMin, heMin, hmin⟩ :=
    Finset.exists_min_image S.support (fun e => e 0) hsupport
  obtain ⟨⟨u,v⟩, rfl⟩ := expo_surjective eMax
  obtain ⟨⟨r,t⟩, rfl⟩ := expo_surjective eMin
  have hmax' : ∀ e ∈ S.support, e 0 ≤ u := by
    simpa [expo] using hmax
  have hmin' : ∀ e ∈ S.support, r ≤ e 0 := by
    simpa [expo] using hmin
  have hP := leadingFace_power_endpoint_pair P S ν ρ s d u v r t degree
    hS hν hs hhom heMax heMin hmax' hmin' hPface
  have hQ := leadingFace_power_endpoint_pair Q S μ ρ s n u v r t degree
    hS hμ hs hhom heMax heMin hmax' hmin' hQface
  exact ⟨u, v, r, t, hP.1, hQ.1, hP.2.1, hQ.2.1,
    (fun e he => ⟨hP.2.2.2 e he, hP.2.2.1 e he⟩),
    (fun e he => ⟨hQ.2.2.2 e he, hQ.2.2.1 e he⟩)⟩

/-- Every primitive positive-sum direction of an actual counterexample pair
has a positive coprime normalization of the two face weights. -/
theorem counterexample_reduced_face_weight_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      (vDeg ρ σ Q.1).toNat * d = (vDeg ρ σ P.1).toNat * n := by
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  let m : ℕ := (vDeg ρ σ P.1).toNat
  let ω : ℕ := (vDeg ρ σ Q.1).toNat
  have hm : 0 < m := by omega
  have hω : 0 < ω := by omega
  obtain ⟨d, n, hcop, hmEq, hωEq⟩ := Nat.exists_coprime m ω
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0, zero_mul] at hmEq
    omega
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, zero_mul] at hωEq
    omega
  refine ⟨n, d, hn, hd, hcop, ?_⟩
  change ω * d = m * n
  calc
    ω * d = (n * Nat.gcd m ω) * d := congrArg (· * d) hωEq
    _ = (d * Nat.gcd m ω) * n := by ac_rfl
    _ = m * n := congrArg (· * n) hmEq.symm

/-- Proportional occupied extreme endpoints exist in every strict negative
direction of an actual counterexample pair; the reduced ratio is selected
from its positive weights rather than supplied as a premise. -/
theorem counterexample_strict_negative_face_proportional_endpoints
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ))) :
    ∃ n d u v r t : ℕ,
      0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      expo (d * u) (d * v) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      expo (n * u) (n * v) ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support ∧
      expo (d * r) (d * t) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      expo (n * r) (n * t) ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support ∧
      (∀ e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support,
        d * r ≤ e 0 ∧ e 0 ≤ d * u) ∧
      (∀ e ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support,
        n * r ≤ e 0 ∧ e 0 ≤ n * u) := by
  obtain ⟨n, d, hn, hd, hcop, hratio⟩ :=
    counterexample_reduced_face_weight_ratio P Q hpair ρ (-(s : ℤ)) hdir
  obtain ⟨u, v, r, t, hpMax, hqMax, hpMin, hqMin, hpBounds, hqBounds⟩ :=
    counterexample_common_face_proportional_endpoints
      P Q hpair ρ s hs hdir n d hn hd hcop hratio
  exact ⟨n, d, u, v, r, t, hn, hd, hcop,
    hpMax, hqMax, hpMin, hqMin, hpBounds, hqBounds⟩

end Dixmier.Weyl
