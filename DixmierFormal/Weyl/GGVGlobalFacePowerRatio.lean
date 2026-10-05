/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVGlobalLeadingPoissonZero
public import DixmierFormal.Weyl.CommonPowerFactorization
public import DixmierFormal.Weyl.HomogeneousRoot

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Common-power relation for the actual faces of a counterexample pair

The exact pair supplies positive weights and a zero leading Poisson bracket
in every primitive positive-sum direction. Thus its two actual leading faces
satisfy the homogeneous power relation. This is the algebraic power equality
used before choosing the common primitive root in G13 Theorem 2.11.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Every counterexample pair has a nonzero scalar power relation between its
two actual leading faces in every allowed direction. The exponents are their
positive weighted degrees, not a bound on the mate's order. -/
theorem counterexample_leading_faces_power_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) :
    ∃ (m ω : ℕ) (c : ℂ),
      0 < m ∧ 0 < ω ∧ c ≠ 0 ∧
      (m : ℤ) = vDeg ρ σ P.1 ∧
      (ω : ℤ) = vDeg ρ σ Q.1 ∧
      (leadingForm ρ σ Q.1) ^ m =
        MvPolynomial.C c * (leadingForm ρ σ P.1) ^ ω := by
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  let m : ℕ := (vDeg ρ σ P.1).toNat
  let ω : ℕ := (vDeg ρ σ Q.1).toNat
  have hm : 0 < m := by omega
  have hω : 0 < ω := by omega
  have hmcast : (m : ℤ) = vDeg ρ σ P.1 := by omega
  have hωcast : (ω : ℤ) = vDeg ρ σ Q.1 := by omega
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous (wt ρ σ) m := by
    rw [hmcast]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hQhom : (leadingForm ρ σ Q.1).IsWeightedHomogeneous (wt ρ σ) ω := by
    rw [hωcast]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt ρ σ) (n := vDeg ρ σ Q.1)
  obtain ⟨c, hc, hpow⟩ := homogeneous_poisson_power_ratio
    (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) ρ σ m ω
    hm hω (leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos)
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos)
    hQhom hPhom
    (counterexample_leadingPoisson_zero_all_directions P Q hpair ρ σ hdir)
  exact ⟨m, ω, c, hm, hω, hc, hmcast, hωcast, hpow⟩

/-- Prime-factor multiplicities in the two actual faces obey the same
weighted-degree ratio, with no chosen common root or mate-order bound. -/
theorem counterexample_leading_faces_prime_multiplicity_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (p : MvPolynomial (Fin 2) ℂ) (hp : Prime p) :
    ∃ (m ω : ℕ), 0 < m ∧ 0 < ω ∧
      (m : ℤ) = vDeg ρ σ P.1 ∧
      (ω : ℤ) = vDeg ρ σ Q.1 ∧
      m * multiplicity p (leadingForm ρ σ Q.1) =
        ω * multiplicity p (leadingForm ρ σ P.1) := by
  obtain ⟨m, ω, c, hm, hω, hc, hmcast, hωcast, hpow⟩ :=
    counterexample_leading_faces_power_ratio P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  exact ⟨m, ω, hm, hω, hmcast, hωcast,
    multiplicity_power_ratio (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1)
      c m ω (leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos)
      (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos) hc hpow p hp⟩

/-- If the two positive face weights have reduced ratio `n/d`, the first
actual leading face is a scalar `d`-th power. This extraction is unconditional
apart from the stated arithmetic ratio; no primitive common root is assumed. -/
theorem counterexample_first_leading_face_power_of_coprime_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (n d : ℕ) (hcop : Nat.Coprime d n)
    (hratio : (vDeg ρ σ Q.1).toNat * d =
      (vDeg ρ σ P.1).toNat * n) :
    ∃ (ν : ℂ) (S : MvPolynomial (Fin 2) ℂ),
      ν ≠ 0 ∧ leadingForm ρ σ P.1 = MvPolynomial.C ν * S ^ d := by
  obtain ⟨m, ω, c, hm, hω, hc, hmcast, hωcast, hpow⟩ :=
    counterexample_leading_faces_power_ratio P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hmNat : m = (vDeg ρ σ P.1).toNat := by omega
  have hωNat : ω = (vDeg ρ σ Q.1).toNat := by omega
  exact bivariate_scalar_power_of_coprime_ratio
    (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) m ω n d c
    (leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos)
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos)
    hc (by simpa only [hmNat, hωNat] using hratio) hm hcop hpow

/-- Both actual faces are proper powers whenever the reduced weight ratio
has numerator and denominator greater than one. The two roots constructed
here are not yet identified with a single primitive common root. -/
theorem counterexample_both_leading_faces_powers_of_coprime_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (n d : ℕ) (hcop : Nat.Coprime d n)
    (hratio : (vDeg ρ σ Q.1).toNat * d =
      (vDeg ρ σ P.1).toNat * n) :
    (∃ (ν : ℂ) (S : MvPolynomial (Fin 2) ℂ),
      ν ≠ 0 ∧ leadingForm ρ σ P.1 = MvPolynomial.C ν * S ^ d) ∧
    (∃ (μ : ℂ) (T : MvPolynomial (Fin 2) ℂ),
      μ ≠ 0 ∧ leadingForm ρ σ Q.1 = MvPolynomial.C μ * T ^ n) := by
  obtain ⟨m, ω, c, hm, hω, hc, hmcast, hωcast, hpow⟩ :=
    counterexample_leading_faces_power_ratio P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hmNat : m = (vDeg ρ σ P.1).toNat := by omega
  have hωNat : ω = (vDeg ρ σ Q.1).toNat := by omega
  exact bivariate_both_scalar_powers_of_coprime_ratio
    (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) m ω n d c
    (leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos)
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos)
    hc (by simpa only [hmNat, hωNat] using hratio) hm hω hcop hpow

/-- The actual faces of a counterexample pair have one common bivariate
root at any positive reduced coprime weight ratio. Homogeneity and
primitive-power normalization of this root are separate source steps. -/
theorem counterexample_leading_faces_common_root_of_coprime_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hratio : (vDeg ρ σ Q.1).toNat * d =
      (vDeg ρ σ P.1).toNat * n) :
    ∃ (S : MvPolynomial (Fin 2) ℂ) (ν μ : ℂ),
      S ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ 0 ∧
      leadingForm ρ σ P.1 = MvPolynomial.C ν * S ^ d ∧
      leadingForm ρ σ Q.1 = MvPolynomial.C μ * S ^ n := by
  obtain ⟨m, ω, c, hm, hω, hc, hmcast, hωcast, hpow⟩ :=
    counterexample_leading_faces_power_ratio P Q hpair ρ σ hdir
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) ρ σ hdir
  have hmNat : m = (vDeg ρ σ P.1).toNat := by omega
  have hωNat : ω = (vDeg ρ σ Q.1).toNat := by omega
  exact bivariate_common_root_of_coprime_ratio
    (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) m ω n d c
    (leadingForm_ne_zero_of_vDeg_pos Q ρ σ hQpos)
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hPpos)
    hc (by simpa only [hmNat, hωNat] using hratio)
    hm hω hn hd hcop hpow

/-- The common root can be chosen weighted homogeneous, and its integer
weight scales to the first face weight. This is the homogeneous common-base
form of the algebraic conclusion; primitive-power normalization is separate. -/
theorem counterexample_leading_faces_homogeneous_common_root
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hratio : (vDeg ρ σ Q.1).toNat * d =
      (vDeg ρ σ P.1).toNat * n) :
    ∃ (S : MvPolynomial (Fin 2) ℂ) (ν μ : ℂ) (r : ℤ),
      S ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ 0 ∧
      IsWeightedHomogeneous (wt ρ σ) S r ∧
      vDeg ρ σ P.1 = (d : ℤ) * r ∧
      leadingForm ρ σ P.1 = MvPolynomial.C ν * S ^ d ∧
      leadingForm ρ σ Q.1 = MvPolynomial.C μ * S ^ n := by
  obtain ⟨S, ν, μ, hS, hν, hμ, hPshape, hQshape⟩ :=
    counterexample_leading_faces_common_root_of_coprime_ratio
      P Q hpair ρ σ hdir n d hn hd hcop hratio
  have hPhom : (leadingForm ρ σ P.1).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt ρ σ) (n := vDeg ρ σ P.1)
  have hSpowhom : (S ^ d).IsWeightedHomogeneous
      (wt ρ σ) (vDeg ρ σ P.1) := by
    intro a ha
    apply hPhom
    have hscaled : a ∈ (MvPolynomial.C ν * S ^ d).support := by
      rw [MvPolynomial.C_mul', MvPolynomial.support_smul_eq hν]
      exact mem_support_iff.mpr ha
    exact mem_support_iff.mp (hPshape ▸ hscaled)
  obtain ⟨r, hrhom, hrweight⟩ :=
    weighted_homogeneous_root_of_power S ρ σ (vDeg ρ σ P.1) d hS hd hSpowhom
  exact ⟨S, ν, μ, r, hS, hν, hμ, hrhom, hrweight, hPshape, hQshape⟩

end Dixmier.Weyl
