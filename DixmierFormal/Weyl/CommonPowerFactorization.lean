/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HomogeneousPowerRatio
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.MvPolynomial.Nilpotent

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Prime-factor multiplicities in a homogeneous power equality

The power identity from the Poisson equation gives an equality of every
prime-factor exponent. This uses extended multiplicities and does not
require a normalization choice for multivariate polynomials. The remaining
primitive-power step is arithmetic on these exponents.
-/

namespace Dixmier.Weyl

open MvPolynomial
open scoped Classical

/-- A nonzero scalar contributes zero multiplicity for every prime
multivariate polynomial. -/
theorem emultiplicity_C_ne_zero
    (p : MvPolynomial (Fin 2) ℂ) (hp : Prime p)
    (c : ℂ) (hc : c ≠ 0) :
    emultiplicity p (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) = 0 := by
  have hu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) :=
    hc.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  exact emultiplicity_of_isUnit_right hp.not_isUnit hu

/-- Every prime multiplicity in `B^m = c R^ω` satisfies the corresponding
integer exponent equation. The scalar coefficient has no prime factors. -/
theorem emultiplicity_power_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hc : c ≠ 0) (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (p : MvPolynomial (Fin 2) ℂ) (hp : Prime p) :
    m * emultiplicity p B = ω * emultiplicity p R := by
  have hf := congrArg (emultiplicity p) hpower
  rw [emultiplicity_pow hp, emultiplicity_mul hp,
    emultiplicity_C_ne_zero p hp c hc, zero_add, emultiplicity_pow hp] at hf
  exact hf

/-- A nonzero polynomial has finite multiplicity at every prime factor. -/
theorem prime_multiplicity_finite
    (R p : MvPolynomial (Fin 2) ℂ) (hR : R ≠ 0) (hp : Prime p) :
    FiniteMultiplicity p R :=
  FiniteMultiplicity.of_prime_left hp hR

/-- Natural-number form of the prime-by-prime exponent identity. -/
theorem multiplicity_power_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (p : MvPolynomial (Fin 2) ℂ) (hp : Prime p) :
    m * multiplicity p B = ω * multiplicity p R := by
  have hfinB := prime_multiplicity_finite B p hB hp
  have hfinR := prime_multiplicity_finite R p hR hp
  have h := emultiplicity_power_ratio B R c m ω hc hpower p hp
  rw [hfinB.emultiplicity_eq_multiplicity,
    hfinR.emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

/-- A factor-exponent profile is primitive if no integer greater than one
divides all of its prime multiplicities. -/
def PrimitiveFactorProfile (R : MvPolynomial (Fin 2) ℂ) : Prop :=
  ∀ d : ℕ, 1 < d → ∃ p : MvPolynomial (Fin 2) ℂ,
    Prime p ∧ ¬ d ∣ multiplicity p R

/-- The associate factor count agrees with ordinary prime multiplicity.
This avoids choosing normalized multivariate factors. -/
theorem associates_count_eq_multiplicity
    (R p : MvPolynomial (Fin 2) ℂ) (hR : R ≠ 0) (hp : Prime p) :
    Associates.count (Associates.mk p) (Associates.mk R).factors = multiplicity p R := by
  classical
  have hirr : Irreducible (Associates.mk p) :=
    Associates.irreducible_mk.mpr hp.irreducible
  have hmk : (Associates.mk R) ≠ 0 := Associates.mk_ne_zero.mpr hR
  apply Nat.le_antisymm
  · apply (prime_multiplicity_finite R p hR hp).pow_dvd_iff_le_multiplicity.mp
    apply Associates.dvd_of_mk_le_mk
    rw [Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hmk hirr).mpr le_rfl
  · apply (Associates.prime_pow_dvd_iff_le hmk hirr).mp
    rw [← Associates.mk_pow]
    exact Associates.mk_le_mk_of_dvd
      ((prime_multiplicity_finite R p hR hp).pow_dvd_iff_le_multiplicity.mpr le_rfl)

/-- A nonzero polynomial which is not a scalar multiple of a proper power
has a primitive prime-factor exponent profile. -/
theorem primitive_factor_profile_of_no_proper_power
    (R : MvPolynomial (Fin 2) ℂ) (hR : R ≠ 0)
    (hnot : ∀ d : ℕ, 1 < d → ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
      μ ≠ 0 → R ≠ MvPolynomial.C μ * S ^ d) :
    PrimitiveFactorProfile R := by
  classical
  intro d hd
  by_contra hn
  have hall : ∀ p : MvPolynomial (Fin 2) ℂ, Prime p → d ∣ multiplicity p R := by
    intro p hp
    by_contra hnd
    exact hn ⟨p, hp, hnd⟩
  have hmk : (Associates.mk R) ≠ 0 := Associates.mk_ne_zero.mpr hR
  have hcounts : ∀ p : Associates (MvPolynomial (Fin 2) ℂ),
      Irreducible p → d ∣ Associates.count p (Associates.mk R).factors := by
    intro p hp
    let q : MvPolynomial (Fin 2) ℂ := Quot.out p
    have hqmk : Associates.mk q = p := Associates.quot_out p
    have hqirr : Irreducible q :=
      Associates.irreducible_mk.mp (hqmk.symm ▸ hp)
    have hqprime : Prime q :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirr
    rw [← hqmk, associates_count_eq_multiplicity R q hR hqprime]
    exact hall q hqprime
  obtain ⟨b, hb⟩ := Associates.is_pow_of_dvd_count hmk hcounts
  let S : MvPolynomial (Fin 2) ℂ := Quot.out b
  have hS : Associates.mk S = b := Associates.quot_out b
  have hassoc : Associated R (S ^ d) := by
    apply Associates.mk_eq_mk_iff_associated.mp
    rw [Associates.mk_pow, hS]
    exact hb
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨μ, hμ, huC⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  apply hnot d hd S μ hμ.ne_zero
  rw [huC] at hu
  calc
    R = S ^ d * MvPolynomial.C μ := hu.symm
    _ = MvPolynomial.C μ * S ^ d := mul_comm _ _

/-- A scalar multiple of a proper power has every prime multiplicity
divisible by the exponent. -/
theorem multiplicity_dvd_of_scalar_proper_power
    (R S p : MvPolynomial (Fin 2) ℂ) (μ : ℂ) (d : ℕ)
    (hR : R ≠ 0) (hd : 1 < d) (hμ : μ ≠ 0)
    (hpower : R = MvPolynomial.C μ * S ^ d) (hp : Prime p) :
    d ∣ multiplicity p R := by
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : d ≠ 0), mul_zero] at hpower
    exact hR hpower
  have hf := congrArg (emultiplicity p) hpower
  rw [emultiplicity_mul hp, emultiplicity_C_ne_zero p hp μ hμ,
    zero_add, emultiplicity_pow hp] at hf
  have hfinR := prime_multiplicity_finite R p hR hp
  have hfinS := prime_multiplicity_finite S p hS hp
  rw [hfinR.emultiplicity_eq_multiplicity,
    hfinS.emultiplicity_eq_multiplicity] at hf
  have hnat : multiplicity p R = d * multiplicity p S := by exact_mod_cast hf
  rw [hnat]
  exact dvd_mul_right d _

/-- For a nonzero bivariate polynomial, the factor profile is primitive
exactly when it is not a scalar multiple of any proper polynomial power. -/
theorem primitive_factor_profile_iff_no_proper_power
    (R : MvPolynomial (Fin 2) ℂ) (hR : R ≠ 0) :
    PrimitiveFactorProfile R ↔
      ∀ d : ℕ, 1 < d → ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
        μ ≠ 0 → R ≠ MvPolynomial.C μ * S ^ d := by
  constructor
  · intro hprim d hd S μ hμ hpower
    obtain ⟨p, hp, hndvd⟩ := hprim d hd
    exact hndvd (multiplicity_dvd_of_scalar_proper_power R S p μ d
      hR hd hμ hpower hp)
  · exact primitive_factor_profile_of_no_proper_power R hR

/-- A primitive factor profile in a power equality forces the first exponent
to divide the second, independently of any degree or support bound. -/
theorem exponent_divides_of_primitive_factor_profile
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hm : 0 < m) (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (hprim : PrimitiveFactorProfile R) : m ∣ ω := by
  by_contra hnot
  obtain ⟨a, b, hab, hm', hω'⟩ := Nat.exists_coprime m ω
  have hapos : 0 < a := by
    by_contra h
    have ha : a = 0 := by omega
    rw [ha] at hm'
    omega
  have ha : 1 < a := by
    by_contra h
    have ha1 : a = 1 := by omega
    rw [ha1, one_mul] at hm'
    exact hnot (hm' ▸ Nat.gcd_dvd_right m ω)
  obtain ⟨p, hp, hndvd⟩ := hprim a ha
  have hmult := multiplicity_power_ratio B R c m ω hB hR hc hpower p hp
  have hgpos : 0 < Nat.gcd m ω := Nat.gcd_pos_of_pos_left ω hm
  have hsmall : a * multiplicity p B = b * multiplicity p R := by
    have hh : Nat.gcd m ω * (a * multiplicity p B) =
        Nat.gcd m ω * (b * multiplicity p R) := by
      calc
        _ = (a * Nat.gcd m ω) * multiplicity p B := by ring
        _ = m * multiplicity p B := congrArg (· * multiplicity p B) hm'.symm
        _ = ω * multiplicity p R := hmult
        _ = (b * Nat.gcd m ω) * multiplicity p R :=
          congrArg (· * multiplicity p R) hω'
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hh
  have hadvd : a ∣ b * multiplicity p R := by
    rw [← hsmall]
    exact dvd_mul_right a _
  exact hndvd ((hab.dvd_mul_left).mp hadvd)

/-- The proper-power conclusion after exponent divisibility: the second
face is a scalar times an integer power of the first face. The comparison
uses integral closure to cancel equal positive powers up to association,
then identifies every multivariate-polynomial unit as a scalar. -/
theorem scalar_power_of_divisible_exponents
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hm : 0 < m) (hc : c ≠ 0)
    (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (hdiv : m ∣ ω) :
    ∃ (ν : ℂ) (k : ℕ), ν ≠ 0 ∧ ω = m * k ∧ B = MvPolynomial.C ν * R ^ k := by
  classical
  obtain ⟨k, hk⟩ := hdiv
  have hC : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) :=
    hc.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hpow : Associated (B ^ m) ((R ^ k) ^ m) := by
    have hpowR : R ^ ω = (R ^ k) ^ m := by
      calc
        R ^ ω = R ^ (m * k) := by rw [hk]
        _ = R ^ (k * m) := by rw [mul_comm]
        _ = (R ^ k) ^ m := pow_mul R k m
    exact (Associated.of_eq hpower).trans
      (hpowR ▸ (associated_unit_mul_left (R ^ ω) (MvPolynomial.C c) hC))
  obtain ⟨u, hu⟩ := ((Associated.pow_iff hm.ne').mp hpow).symm
  obtain ⟨ν, hν, huC⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  refine ⟨ν, k, ?_, hk, ?_⟩
  · exact hν.ne_zero
  · rw [huC] at hu
    rw [← hu]
    ring

/-- The complete algebraic consequence of a primitive factor profile:
any competing power in the same homogeneous Poisson centralizer is an
integer power of the primitive face, up to a nonzero scalar. -/
theorem scalar_power_of_primitive_factor_profile
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hm : 0 < m) (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (hprim : PrimitiveFactorProfile R) :
    ∃ (ν : ℂ) (k : ℕ), ν ≠ 0 ∧ ω = m * k ∧ B = MvPolynomial.C ν * R ^ k := by
  exact scalar_power_of_divisible_exponents B R c m ω hm hc hpower
    (exponent_divides_of_primitive_factor_profile B R c m ω hm hB hR hc hpower hprim)

/-- The paper-facing common-power consequence, stated with the usual
"not a scalar multiple of a proper power" hypothesis. -/
theorem scalar_power_of_no_proper_power
    (B R : MvPolynomial (Fin 2) ℂ) (c : ℂ) (m ω : ℕ)
    (hm : 0 < m) (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hpower : B ^ m = MvPolynomial.C c * R ^ ω)
    (hnot : ∀ d : ℕ, 1 < d → ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
      μ ≠ 0 → R ≠ MvPolynomial.C μ * S ^ d) :
    ∃ (ν : ℂ) (k : ℕ), ν ≠ 0 ∧ ω = m * k ∧ B = MvPolynomial.C ν * R ^ k := by
  exact scalar_power_of_primitive_factor_profile B R c m ω hm hB hR hc hpower
    (primitive_factor_profile_of_no_proper_power R hR hnot)

/-- A coprime reduced ratio in a bivariate scalar power equality forces a
genuine polynomial power. This is the multivariate counterpart of the
ramified one-variable extraction, and does not choose a primitive common
root in advance. -/
theorem bivariate_scalar_power_of_coprime_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (m ω n d : ℕ) (c : ℂ)
    (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hratio : ω * d = m * n) (hm : 0 < m)
    (hcop : Nat.Coprime d n)
    (hpow : B ^ m = MvPolynomial.C c * R ^ ω) :
    ∃ (ν : ℂ) (S : MvPolynomial (Fin 2) ℂ),
      ν ≠ 0 ∧ R = MvPolynomial.C ν * S ^ d := by
  classical
  have hmkR : (Associates.mk R) ≠ 0 := Associates.mk_ne_zero.mpr hR
  have hmkB : (Associates.mk B) ≠ 0 := Associates.mk_ne_zero.mpr hB
  have hCunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) :=
    hc.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hmkpow : (Associates.mk B) ^ m = (Associates.mk R) ^ ω := by
    calc
      (Associates.mk B) ^ m = Associates.mk (B ^ m) := (Associates.mk_pow B m).symm
      _ = Associates.mk (MvPolynomial.C c * R ^ ω) := congrArg Associates.mk hpow
      _ = Associates.mk (MvPolynomial.C c) * Associates.mk (R ^ ω) :=
        Associates.mk_mul_mk.symm
      _ = (Associates.mk R) ^ ω := by
        rw [Associates.mk_eq_one.mpr hCunit, one_mul, Associates.mk_pow]
  have hcounts : ∀ p : Associates (MvPolynomial (Fin 2) ℂ),
      Irreducible p → d ∣ Associates.count p (Associates.mk R).factors := by
    intro p hp
    have heq := congrArg (fun z : Associates (MvPolynomial (Fin 2) ℂ) =>
      Associates.count p z.factors) hmkpow
    rw [Associates.count_pow hmkB hp m,
      Associates.count_pow hmkR hp ω] at heq
    have hmul : m * (n * Associates.count p (Associates.mk R).factors) =
        m * (d * Associates.count p (Associates.mk B).factors) := by
      calc
        m * (n * Associates.count p (Associates.mk R).factors) =
            (ω * d) * Associates.count p (Associates.mk R).factors := by
              rw [hratio]
              ac_rfl
        _ = d * (ω * Associates.count p (Associates.mk R).factors) := by ac_rfl
        _ = d * (m * Associates.count p (Associates.mk B).factors) := by rw [heq]
        _ = m * (d * Associates.count p (Associates.mk B).factors) := by ac_rfl
    have hcancel : n * Associates.count p (Associates.mk R).factors =
        d * Associates.count p (Associates.mk B).factors :=
      Nat.eq_of_mul_eq_mul_left hm hmul
    apply hcop.dvd_of_dvd_mul_left
    rw [hcancel]
    exact dvd_mul_right d _
  obtain ⟨b, hb⟩ := Associates.is_pow_of_dvd_count hmkR hcounts
  let S : MvPolynomial (Fin 2) ℂ := Quot.out b
  have hSmk : Associates.mk S = b := Associates.quot_out b
  have hassoc : Associated R (S ^ d) := by
    apply Associates.mk_eq_mk_iff_associated.mp
    rw [Associates.mk_pow, hSmk]
    exact hb
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨ν, hν, huC⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  refine ⟨ν, S, hν.ne_zero, ?_⟩
  rw [huC] at hu
  calc
    R = S ^ d * MvPolynomial.C ν := hu.symm
    _ = MvPolynomial.C ν * S ^ d := mul_comm _ _

/-- The same coprime ratio extracts powers on both sides of the equation.
The roots are not yet asserted to coincide; that is the remaining common-root
normalization in the source theorem. -/
theorem bivariate_both_scalar_powers_of_coprime_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (m ω n d : ℕ) (c : ℂ)
    (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hratio : ω * d = m * n) (hm : 0 < m) (hω : 0 < ω)
    (hcop : Nat.Coprime d n)
    (hpow : B ^ m = MvPolynomial.C c * R ^ ω) :
    (∃ (ν : ℂ) (S : MvPolynomial (Fin 2) ℂ),
      ν ≠ 0 ∧ R = MvPolynomial.C ν * S ^ d) ∧
    (∃ (μ : ℂ) (T : MvPolynomial (Fin 2) ℂ),
      μ ≠ 0 ∧ B = MvPolynomial.C μ * T ^ n) := by
  have hfirst := bivariate_scalar_power_of_coprime_ratio
    B R m ω n d c hB hR hc hratio hm hcop hpow
  have hpow' : R ^ ω = MvPolynomial.C c⁻¹ * B ^ m := by
    rw [hpow, ← mul_assoc, ← map_mul]
    simp [hc]
  have hsecond := bivariate_scalar_power_of_coprime_ratio
    R B ω m d n c⁻¹ hR hB (inv_ne_zero hc) hratio.symm hω hcop.symm hpow'
  exact ⟨hfirst, hsecond⟩

/-- A reduced positive weight ratio gives one common polynomial root for
both faces, up to nonzero scalar factors. The proof first extracts the two
powers, then cancels equal positive powers in the associates monoid. -/
theorem bivariate_common_root_of_coprime_ratio
    (B R : MvPolynomial (Fin 2) ℂ) (m ω n d : ℕ) (c : ℂ)
    (hB : B ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0)
    (hratio : ω * d = m * n) (hm : 0 < m) (hω : 0 < ω)
    (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hpow : B ^ m = MvPolynomial.C c * R ^ ω) :
    ∃ (S : MvPolynomial (Fin 2) ℂ) (ν μ : ℂ),
      S ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ 0 ∧
      R = MvPolynomial.C ν * S ^ d ∧
      B = MvPolynomial.C μ * S ^ n := by
  classical
  obtain ⟨⟨ν, S, hν, hRshape⟩, ⟨μ, T, hμ, hBshape⟩⟩ :=
    bivariate_both_scalar_powers_of_coprime_ratio
      B R m ω n d c hB hR hc hratio hm hω hcop hpow
  have hS : S ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hd), mul_zero] at hRshape
    exact hR hRshape
  have hνunit : IsUnit (MvPolynomial.C ν : MvPolynomial (Fin 2) ℂ) :=
    hν.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hμunit : IsUnit (MvPolynomial.C μ : MvPolynomial (Fin 2) ℂ) :=
    hμ.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hmkR : Associates.mk R = (Associates.mk S) ^ d := by
    rw [hRshape, ← Associates.mk_mul_mk, Associates.mk_eq_one.mpr hνunit,
      one_mul, Associates.mk_pow]
  have hmkB : Associates.mk B = (Associates.mk T) ^ n := by
    rw [hBshape, ← Associates.mk_mul_mk, Associates.mk_eq_one.mpr hμunit,
      one_mul, Associates.mk_pow]
  have hcunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) :=
    hc.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hmkpow : (Associates.mk B) ^ m = (Associates.mk R) ^ ω := by
    calc
      (Associates.mk B) ^ m = Associates.mk (B ^ m) := (Associates.mk_pow B m).symm
      _ = Associates.mk (MvPolynomial.C c * R ^ ω) := congrArg Associates.mk hpow
      _ = Associates.mk (MvPolynomial.C c) * Associates.mk (R ^ ω) :=
        Associates.mk_mul_mk.symm
      _ = (Associates.mk R) ^ ω := by
        rw [Associates.mk_eq_one.mpr hcunit, one_mul, Associates.mk_pow]
  have hexp : n * m = d * ω := by simpa only [Nat.mul_comm] using hratio.symm
  have hmkroot : (Associates.mk T) ^ (n * m) =
      (Associates.mk S) ^ (n * m) := by
    calc
      (Associates.mk T) ^ (n * m) = ((Associates.mk T) ^ n) ^ m :=
        pow_mul _ n m
      _ = (Associates.mk B) ^ m := by rw [hmkB]
      _ = (Associates.mk R) ^ ω := hmkpow
      _ = ((Associates.mk S) ^ d) ^ ω := by rw [hmkR]
      _ = (Associates.mk S) ^ (n * m) := by
        rw [← pow_mul]
        exact congrArg (fun k => (Associates.mk S) ^ k) hexp.symm
  have hassocpow : Associated (T ^ (n * m)) (S ^ (n * m)) := by
    apply Associates.mk_eq_mk_iff_associated.mp
    simpa only [Associates.mk_pow] using hmkroot
  have hassoc : Associated T S :=
    (Associated.pow_iff (Nat.ne_of_gt (mul_pos hn hm))).mp hassocpow
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨lam, hlam, huC⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  have hT : T = MvPolynomial.C lam * S := by
    rw [huC] at hu
    calc
      T = S * MvPolynomial.C lam := hu.symm
      _ = MvPolynomial.C lam * S := mul_comm _ _
  refine ⟨S, ν, μ * lam ^ n, hS, hν, mul_ne_zero hμ (pow_ne_zero _ hlam.ne_zero),
    hRshape, ?_⟩
  rw [hBshape, hT]
  simp only [mul_pow, ← map_pow, map_mul]
  ring

/-- A commuting positive-weight homogeneous face is a scalar integer power
of a face with no scalar proper-power decomposition. -/
theorem homogeneous_poisson_scalar_power_of_no_proper_power
    (B R : MvPolynomial (Fin 2) ℂ) (ρ σ : ℤ) (m ω : ℕ)
    (hm : 0 < m) (hω : 0 < ω) (hB0 : B ≠ 0) (hR0 : R ≠ 0)
    (hB : B.IsWeightedHomogeneous (wt ρ σ) ω)
    (hR : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hbr : poisson B R = 0)
    (hnot : ∀ d : ℕ, 1 < d → ∀ (S : MvPolynomial (Fin 2) ℂ) (μ : ℂ),
      μ ≠ 0 → R ≠ MvPolynomial.C μ * S ^ d) :
    ∃ (ν : ℂ) (k : ℕ), ν ≠ 0 ∧ ω = m * k ∧ B = MvPolynomial.C ν * R ^ k := by
  obtain ⟨c, hc, hpow⟩ := homogeneous_poisson_power_ratio B R ρ σ m ω
    hm hω hB0 hR0 hB hR hbr
  exact scalar_power_of_no_proper_power B R c m ω hm hB0 hR0 hc hpow hnot

end Dixmier.Weyl
