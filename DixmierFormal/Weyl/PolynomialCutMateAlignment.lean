/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialRamifiedCutEndpoint
public import DixmierFormal.Weyl.HomogeneousPowerRatio
public import DixmierFormal.Scalar.Section6Roots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Common root orders on commuting polynomial Weyl faces

The homogeneous Poisson power identity descends to the actual univariate
cut polynomials. This is the algebraic part of the mate alignment used in
G13 Proposition 5.3; the new supporting direction is separate.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

private theorem cutPoly_eval_power_ratio
    (P Q : A1 ℂ) (ρ σ : ℤ) (m n : ℕ) (c : ℂ)
    (hpow : (leadingForm ρ σ P.1) ^ m =
      MvPolynomial.C c * (leadingForm ρ σ Q.1) ^ n) :
    (cutPoly ρ σ P.1) ^ m =
      Polynomial.C c * (cutPoly ρ σ Q.1) ^ n := by
  have h := congrArg
    (MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 2 => if i = 0 then (1 : ℂ[X]) else Polynomial.X)) hpow
  simpa [cutPoly, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul]
    using h

/-- A genuine positive-`ρ` source face stays nonzero after the
`x = 1` specialization defining the cut polynomial. -/
theorem cutPoly_ne_zero_of_InDir (P : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdir : InDir ρ σ P.1) :
    cutPoly ρ σ P.1 ≠ 0 := by
  obtain ⟨d₁,d₂,hd₁,hd₂,hne⟩ := Finset.one_lt_card_iff.mp hdir
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d₁
  obtain ⟨hs,hw⟩ := polynomialFace_point_source_data P ρ σ i j hd₁
  have hc := cutPoly_coeff_at_face_point P ρ σ i j hρ hw
  intro hz
  have hcoeff : MvPolynomial.coeff (expo i j)
      (leadingForm ρ σ P.1) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd₁
  exact hcoeff (by simpa [hz] using hc.symm)

/-- A zero leading Poisson bracket with positive face weights gives a
power identity for the two actual source cut polynomials. No mate-order,
mass, or support-size bound is imposed. -/
theorem cutPoly_power_ratio_of_leadingPoisson_zero
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hbr : poisson (leadingForm ρ σ P.1)
      (leadingForm ρ σ Q.1) = 0)
    (hPne : leadingForm ρ σ P.1 ≠ 0)
    (hQne : leadingForm ρ σ Q.1 ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      (cutPoly ρ σ P.1) ^ (vDeg ρ σ Q.1).toNat =
        Polynomial.C c *
          (cutPoly ρ σ Q.1) ^ (vDeg ρ σ P.1).toNat := by
  let n : ℕ := (vDeg ρ σ P.1).toNat
  let m : ℕ := (vDeg ρ σ Q.1).toNat
  have hnc : (n : ℤ) = vDeg ρ σ P.1 := Int.toNat_of_nonneg (le_of_lt hP)
  have hmc : (m : ℤ) = vDeg ρ σ Q.1 := Int.toNat_of_nonneg (le_of_lt hQ)
  have hn : 0 < n := by
    rw [← hnc] at hP
    exact_mod_cast hP
  have hm : 0 < m := by
    rw [← hmc] at hQ
    exact_mod_cast hQ
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) n := by
    simpa only [leadingForm, hnc] using
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (φ := symbol P.1) (w := wt ρ σ)
        (n := vDeg ρ σ P.1))
  obtain ⟨c,hc,hpow⟩ := homogeneous_poisson_power_ratio
    (leadingForm ρ σ P.1) (leadingForm ρ σ Q.1)
    ρ σ m n hm hn hPne hQne hPhom (by
      simpa only [leadingForm, hmc] using
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
          (φ := symbol Q.1) (w := wt ρ σ)
          (n := vDeg ρ σ Q.1))) hbr
  exact ⟨c,hc,cutPoly_eval_power_ratio P Q ρ σ m n c hpow⟩

/-- The two source cut polynomials have proportional multiplicity at
every complex root. In particular, a selected root of `P` is also a
root of `Q`. This is the root-order portion of G13 mate alignment. -/
theorem cutPoly_rootMultiplicity_ratio_of_leadingPoisson_zero
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ)
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hbr : poisson (leadingForm ρ σ P.1)
      (leadingForm ρ σ Q.1) = 0) :
    ∀ a : ℂ,
      (vDeg ρ σ Q.1).toNat *
          (cutPoly ρ σ P.1).rootMultiplicity a =
        (vDeg ρ σ P.1).toNat *
          (cutPoly ρ σ Q.1).rootMultiplicity a := by
  have hpne := cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
  have hqne := cutPoly_ne_zero_of_InDir Q ρ σ hρ hdirQ
  have hPne : leadingForm ρ σ P.1 ≠ 0 := by
    intro hz
    simp [InDir, hz] at hdirP
  have hQne : leadingForm ρ σ Q.1 ≠ 0 := by
    intro hz
    simp [InDir, hz] at hdirQ
  obtain ⟨c,hc,hpow⟩ := cutPoly_power_ratio_of_leadingPoisson_zero
    P Q ρ σ hP hQ hbr hPne hQne
  intro a
  have h := congrArg (Polynomial.rootMultiplicity a) hpow
  rw [Dixmier.section6_rootMultiplicity_pow,
    Polynomial.rootMultiplicity_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
        (pow_ne_zero _ hqne)),
    Polynomial.rootMultiplicity_C,
    zero_add,
    Dixmier.section6_rootMultiplicity_pow] at h
  exact h

/-- In the exact-pair range of G13 Proposition 5.3, the root chosen
from `P` is necessarily a root of the unrestricted mate's cut
polynomial, with the precise multiplicity ratio dictated by the two
weighted degrees. -/
theorem exactPair_cutPoly_common_root_and_multiplicity
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (a : ℂ) (ha : (cutPoly ρ σ P.1).IsRoot a) :
    (cutPoly ρ σ Q.1).IsRoot a ∧
      (vDeg ρ σ Q.1).toNat *
          (cutPoly ρ σ P.1).rootMultiplicity a =
        (vDeg ρ σ P.1).toNat *
          (cutPoly ρ σ Q.1).rootMultiplicity a := by
  have hbrQP := leadingPoisson_eq_zero_of_exact_commutator
    P Q ρ σ hdir.2 hQP (by omega)
  have hbrPQ : poisson (leadingForm ρ σ P.1)
      (leadingForm ρ σ Q.1) = 0 := by
    have hanti : poisson (leadingForm ρ σ P.1)
        (leadingForm ρ σ Q.1) =
          -poisson (leadingForm ρ σ Q.1)
            (leadingForm ρ σ P.1) := by
      unfold poisson
      ring
    rw [hanti,hbrQP]
    simp
  have hratio := cutPoly_rootMultiplicity_ratio_of_leadingPoisson_zero
    P Q ρ σ hρ hP hQ hdirP hdirQ hbrPQ a
  have hpne := cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
  have hqne := cutPoly_ne_zero_of_InDir Q ρ σ hρ hdirQ
  have hrootP : 0 < (cutPoly ρ σ P.1).rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hpne).mpr ha
  have hweightQ : 0 < (vDeg ρ σ Q.1).toNat := by
    have hcast : (((vDeg ρ σ Q.1).toNat : ℕ) : ℤ) =
      vDeg ρ σ Q.1 := Int.toNat_of_nonneg (le_of_lt hQ)
    rw [← hcast] at hQ
    exact_mod_cast hQ
  have hrootQ : 0 < (cutPoly ρ σ Q.1).rootMultiplicity a := by
    have hproduct : 0 < (vDeg ρ σ P.1).toNat *
        (cutPoly ρ σ Q.1).rootMultiplicity a := by
      rw [← hratio]
      exact Nat.mul_pos hweightQ hrootP
    by_contra hn
    have hz : (cutPoly ρ σ Q.1).rootMultiplicity a = 0 := by omega
    rw [hz, mul_zero] at hproduct
    exact (Nat.not_lt_zero _) hproduct
  exact ⟨(Polynomial.rootMultiplicity_pos hqne).mp hrootQ, hratio⟩

/-- A single maximum-root cut transports an exact pair and places
occupied endpoints for both operators on their sheared old faces. The
two endpoint derivative orders satisfy the source weight ratio. This
does not yet identify the common *new* Newton direction. -/
theorem exactPair_maxRoot_cut_mate_oldFace_endpoints
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1) :
    let rP := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let rQ := ((l : ℤ) / ρ) * vDeg ρ σ Q.1
    let k := ramifiedCutExponent l ρ σ
    let M := maxRootMult (cutPoly ρ σ P.1)
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c = M ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      (vDeg ρ σ Q.1).toNat * M =
        (vDeg ρ σ P.1).toNat *
          (cutPoly ρ σ Q.1).rootMultiplicity c ∧
      (rP-k*(M : ℤ),M) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      (rQ-k*((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ),
        (cutPoly ρ σ Q.1).rootMultiplicity c) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) ∧
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 := by
  obtain ⟨c,hrootP,hmP,hpointP,hextP,hexact⟩ :=
    polynomialRamifiedCut_exact_pair_maxRoot_extremal
      l hl P Q ρ σ hρ hdiv hdir.2 hdirP hQP
  obtain ⟨hrootQ,hratio⟩ :=
    exactPair_cutPoly_common_root_and_multiplicity
      P Q ρ σ hdir hρ hP hQ hdirP hdirQ hQP hsum c hrootP
  obtain ⟨d₁,d₂,hd₁,hd₂,hne⟩ := Finset.one_lt_card_iff.mp hdirQ
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d₁
  have hQstart := polynomialRamifiedCut_root_start_on_old_face
    l hl Q ρ σ hρ hdiv hdir.2 i j hd₁ c
  refine ⟨c,hrootP,hmP,hrootQ,?_,hpointP,hQstart.1.1,hexact⟩
  rw [hmP] at hratio
  exact hratio

/-- The weighted-degree ratio and the two root orders make both
coordinates of the sheared old-face endpoints proportional. This is
the arithmetic content of G13 Proposition 5.3(7), before identifying
those points as endpoints at a new common direction. -/
theorem cut_oldFace_endpoints_proportional
    (l : ℕ) (ρ σ wP wQ : ℤ) (M N : ℕ)
    (hP : 0 < wP) (hQ : 0 < wQ)
    (hratio : wQ.toNat * M = wP.toNat * N) :
    let k := ramifiedCutExponent l ρ σ
    let rP := ((l : ℤ) / ρ) * wP
    let rQ := ((l : ℤ) / ρ) * wQ
    wQ * (rP-k*(M : ℤ)) = wP * (rQ-k*(N : ℤ)) ∧
      wQ * (M : ℤ) = wP * (N : ℤ) := by
  have hPcast : ((wP.toNat : ℕ) : ℤ) = wP :=
    Int.toNat_of_nonneg (le_of_lt hP)
  have hQcast : ((wQ.toNat : ℕ) : ℤ) = wQ :=
    Int.toNat_of_nonneg (le_of_lt hQ)
  have hratioZ := congrArg (fun a : ℕ => (a : ℤ)) hratio
  push_cast at hratioZ
  rw [hPcast,hQcast] at hratioZ
  constructor
  · calc
      wQ * (((l : ℤ) / ρ) * wP -
          ramifiedCutExponent l ρ σ * (M : ℤ)) =
        (((l : ℤ) / ρ) * wP) * wQ -
          ramifiedCutExponent l ρ σ * (wQ * (M : ℤ)) := by ring
      _ = (((l : ℤ) / ρ) * wQ) * wP -
          ramifiedCutExponent l ρ σ * (wP * (N : ℤ)) := by
            rw [hratioZ]
            ring
      _ = wP * (((l : ℤ) / ρ) * wQ -
          ramifiedCutExponent l ρ σ * (N : ℤ)) := by ring
  · exact hratioZ

/-- A reduced nonintegral weighted-degree ratio forces the selected
root orders to be at least the corresponding reduced denominators.
This extracts the order bound needed in G13's differing-direction
contradiction directly from the paired cut-polynomial multiplicities. -/
theorem reduced_ratio_root_orders_divide
    (wP wQ : ℤ) (d n M N : ℕ)
    (hP : 0 < wP)
    (hweight : wQ * (d : ℤ) = wP * (n : ℤ))
    (hroot : wQ * (M : ℤ) = wP * (N : ℤ))
    (hcop : Nat.Coprime n d)
    : d ∣ M ∧ n ∣ N := by
  have ha := congrArg (fun z : ℤ => z * (M : ℤ)) hweight
  have hb := congrArg (fun z : ℤ => z * (d : ℤ)) hroot
  have hfactor : wP * ((n : ℤ) * (M : ℤ)) =
      wP * ((d : ℤ) * (N : ℤ)) := by
    nlinarith [ha,hb]
  have hcrossZ : (n : ℤ) * (M : ℤ) =
      (d : ℤ) * (N : ℤ) :=
    (mul_left_cancel₀ (ne_of_gt hP)) hfactor
  have hcross : n * M = d * N := by exact_mod_cast hcrossZ
  have hdvd : d ∣ M := by
    apply hcop.symm.dvd_of_dvd_mul_left
    rw [hcross]
    exact dvd_mul_right d N
  have hnvd : n ∣ N := by
    apply hcop.dvd_of_dvd_mul_left
    rw [← hcross]
    exact dvd_mul_right n M
  exact ⟨hdvd, hnvd⟩

/-- Positive selected root orders are at least their corresponding
reduced weight-ratio factors. -/
theorem reduced_ratio_root_orders_ge
    (wP wQ : ℤ) (d n M N : ℕ)
    (hP : 0 < wP)
    (hweight : wQ * (d : ℤ) = wP * (n : ℤ))
    (hroot : wQ * (M : ℤ) = wP * (N : ℤ))
    (hcop : Nat.Coprime n d)
    (hM : 0 < M) (hN : 0 < N) :
    d ≤ M ∧ n ≤ N := by
  obtain ⟨hdvd,hnvd⟩ := reduced_ratio_root_orders_divide
    wP wQ d n M N hP hweight hroot hcop
  exact ⟨Nat.le_of_dvd hM hdvd, Nat.le_of_dvd hN hnvd⟩

/-- The two selected root orders share one positive integer factor
after reduction of their weighted-degree ratio. -/
theorem reduced_ratio_root_orders_common_factor
    (wP wQ : ℤ) (d n M N : ℕ)
    (hP : 0 < wP) (hd : 0 < d)
    (hweight : wQ * (d : ℤ) = wP * (n : ℤ))
    (hroot : wQ * (M : ℤ) = wP * (N : ℤ))
    (hcop : Nat.Coprime n d) (hM : 0 < M) :
    ∃ k : ℕ, 0 < k ∧ M = d * k ∧ N = n * k := by
  obtain ⟨hdvd,_⟩ := reduced_ratio_root_orders_divide
    wP wQ d n M N hP hweight hroot hcop
  obtain ⟨k,hMk⟩ := hdvd
  have hcrossZ : (n : ℤ) * (M : ℤ) =
      (d : ℤ) * (N : ℤ) := by
    have ha := congrArg (fun z : ℤ => z * (M : ℤ)) hweight
    have hb := congrArg (fun z : ℤ => z * (d : ℤ)) hroot
    have hfactor : wP * ((n : ℤ) * (M : ℤ)) =
        wP * ((d : ℤ) * (N : ℤ)) := by nlinarith [ha,hb]
    exact mul_left_cancel₀ (ne_of_gt hP) hfactor
  have hcross : n * M = d * N := by exact_mod_cast hcrossZ
  have hk : 0 < k := by
    by_contra hbad
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hbad
    simp [hk0] at hMk
    omega
  have hNk : N = n * k := by
    rw [hMk] at hcross
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcross.symm)
  exact ⟨k,hk,hMk,hNk⟩

/-- For an exact pair, the selected maximum root and its mate root
have orders at least the denominator and numerator of a reduced
nonintegral weighted-degree ratio. This supplies the root-order part
of the adjacent-direction argument; it does not identify the new
directions. -/
theorem exactPair_maxRoot_cut_root_orders_divide
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      d ∣ (cutPoly ρ σ P.1).rootMultiplicity c ∧
      n ∣ (cutPoly ρ σ Q.1).rootMultiplicity c := by
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,_,_,_⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
  have hratioZ := congrArg (fun a : ℕ => (a : ℤ)) hratio
  push_cast at hratioZ
  rw [Int.toNat_of_nonneg (le_of_lt hP),
      Int.toNat_of_nonneg (le_of_lt hQ)] at hratioZ
  rw [← hmP] at hratioZ
  obtain ⟨hdivP,hdivQ⟩ :=
    reduced_ratio_root_orders_divide
      (vDeg ρ σ P.1) (vDeg ρ σ Q.1) d n
      ((cutPoly ρ σ P.1).rootMultiplicity c)
      ((cutPoly ρ σ Q.1).rootMultiplicity c)
      hP hweight hratioZ hcop
  exact ⟨c,hrootP,hrootQ,hdivP,hdivQ⟩

/-- The exact-pair divisibility result gives positive lower bounds on
both selected root orders. -/
theorem exactPair_maxRoot_cut_root_orders_ge
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      d ≤ (cutPoly ρ σ P.1).rootMultiplicity c ∧
      n ≤ (cutPoly ρ σ Q.1).rootMultiplicity c := by
  obtain ⟨c,hrootP,hrootQ,hdivP,hdivQ⟩ :=
    exactPair_maxRoot_cut_root_orders_divide
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
      d n hweight hcop
  have hPne : cutPoly ρ σ P.1 ≠ 0 :=
    cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
  have hQne : cutPoly ρ σ Q.1 ≠ 0 :=
    cutPoly_ne_zero_of_InDir Q ρ σ hρ hdirQ
  have hmPpos : 0 < (cutPoly ρ σ P.1).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hPne).mpr hrootP
  have hmQpos : 0 < (cutPoly ρ σ Q.1).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hQne).mpr hrootQ
  exact ⟨c,hrootP,hrootQ,
    Nat.le_of_dvd hmPpos hdivP, Nat.le_of_dvd hmQpos hdivQ⟩

end Dixmier.Weyl
