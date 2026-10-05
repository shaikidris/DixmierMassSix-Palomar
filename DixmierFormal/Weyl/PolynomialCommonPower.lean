/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFacePowerRatio
public import DixmierFormal.Weyl.CommonPowerFactorization

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Common-base extraction for complex polynomial faces

This module turns a scalar power identity at coprime reduced weights into
an actual polynomial power. It is intended for the ramified corner argument.
-/

namespace Dixmier.Weyl

/-- A scalar power ratio with coprime reduced weight denominator makes the
first complex polynomial a scalar multiple of that denominator's power. -/
theorem polynomial_scalar_power_of_coprime_ratio
    (f g : Polynomial ℂ) (A D n d : ℕ) (c : ℂ)
    (hf : f ≠ 0) (hg : g ≠ 0) (hc : c ≠ 0)
    (hratio : D * d = A * n) (hA : 0 < A)
    (hcop : Nat.Coprime d n)
    (hpow : f ^ D = Polynomial.C c * g ^ A) :
    ∃ (ν : ℂ) (r : Polynomial ℂ), ν ≠ 0 ∧ f = Polynomial.C ν * r ^ d := by
  classical
  have hmkf : (Associates.mk f) ≠ 0 := Associates.mk_ne_zero.mpr hf
  have hmkg : (Associates.mk g) ≠ 0 := Associates.mk_ne_zero.mpr hg
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hmkpow : (Associates.mk f) ^ D = (Associates.mk g) ^ A := by
    calc
      (Associates.mk f) ^ D = Associates.mk (f ^ D) := (Associates.mk_pow f D).symm
      _ = Associates.mk (Polynomial.C c * g ^ A) := congrArg Associates.mk hpow
      _ = Associates.mk (Polynomial.C c) * Associates.mk (g ^ A) :=
        Associates.mk_mul_mk.symm
      _ = (Associates.mk g) ^ A := by
        rw [Associates.mk_eq_one.mpr hCunit, one_mul, Associates.mk_pow]
  have hcounts : ∀ p : Associates (Polynomial ℂ),
      Irreducible p → d ∣ Associates.count p (Associates.mk f).factors := by
    intro p hp
    have heq := congrArg (fun z : Associates (Polynomial ℂ) =>
      Associates.count p z.factors) hmkpow
    rw [Associates.count_pow hmkf hp D,
      Associates.count_pow hmkg hp A] at heq
    have hmul : A * (n * Associates.count p (Associates.mk f).factors) =
        A * (d * Associates.count p (Associates.mk g).factors) := by
      calc
        A * (n * Associates.count p (Associates.mk f).factors) =
            (D * d) * Associates.count p (Associates.mk f).factors := by
              rw [hratio]
              ac_rfl
        _ = d * (D * Associates.count p (Associates.mk f).factors) := by ac_rfl
        _ = d * (A * Associates.count p (Associates.mk g).factors) := by rw [heq]
        _ = A * (d * Associates.count p (Associates.mk g).factors) := by ac_rfl
    have hcancel : n * Associates.count p (Associates.mk f).factors =
        d * Associates.count p (Associates.mk g).factors :=
      Nat.eq_of_mul_eq_mul_left hA hmul
    apply hcop.dvd_of_dvd_mul_left
    rw [hcancel]
    exact dvd_mul_right d _
  obtain ⟨b, hb⟩ := Associates.is_pow_of_dvd_count hmkf hcounts
  let r : Polynomial ℂ := Quot.out b
  have hrmk : Associates.mk r = b := Associates.quot_out b
  have hassoc : Associated f (r ^ d) := by
    apply Associates.mk_eq_mk_iff_associated.mp
    rw [Associates.mk_pow, hrmk]
    exact hb
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨ν, hν, huC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  refine ⟨ν, r, hν.ne_zero, ?_⟩
  rw [← huC] at hu
  calc
    f = r ^ d * Polynomial.C ν := hu.symm
    _ = Polynomial.C ν * r ^ d := mul_comm _ _

/-- Extract a true common-base power from the first actual top face of an
exact ramified Weyl pair, using its reduced positive weight ratio. -/
theorem ramified_exact_pair_top_face_scalar_power
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ))
    (n d : ℕ)
    (hratio : (ramifiedWeightDeg l hl ρ σ Q).toNat * d =
      (ramifiedWeightDeg l hl ρ σ P).toNat * n)
    (hcop : Nat.Coprime d n) :
    ∃ (ν : ℂ) (r : Polynomial ℂ), ν ≠ 0 ∧
      ramifiedTopFacePolynomial l hl ρ σ P = Polynomial.C ν * r ^ d := by
  obtain ⟨c, hc, hpow⟩ := ramified_exact_pair_top_face_power_ratio
    l hl ρ σ hρ hsum P Q hPne hQne hcomm hA hD hthreshold
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hPne
  have hg := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ Q hQne
  have hAPos : 0 < (ramifiedWeightDeg l hl ρ σ P).toNat := by
    omega
  exact polynomial_scalar_power_of_coprime_ratio
    _ _ _ _ n d c hf hg hc hratio hAPos hcop hpow

/-- A height-two first top face has a quadratic common base once the
reduced denominator power has been extracted. -/
theorem ramified_exact_pair_top_face_quadratic_power
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ))
    (n d : ℕ) (hd : 0 < d)
    (hratio : (ramifiedWeightDeg l hl ρ σ Q).toNat * d =
      (ramifiedWeightDeg l hl ρ σ P).toNat * n)
    (hcop : Nat.Coprime d n)
    (hdegree : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree = 2*d) :
    ∃ (ν : ℂ) (r : Polynomial ℂ), ν ≠ 0 ∧ r.natDegree = 2 ∧
      ramifiedTopFacePolynomial l hl ρ σ P = Polynomial.C ν * r ^ d := by
  obtain ⟨ν, r, hν, hshape⟩ := ramified_exact_pair_top_face_scalar_power
    l hl ρ σ hρ hsum P Q hPne hQne hcomm hA hD hthreshold n d hratio hcop
  have hdeg : d * r.natDegree = d * 2 := by
    rw [hshape, Polynomial.natDegree_C_mul hν,
      Polynomial.natDegree_pow] at hdegree
    simpa only [mul_comm] using hdegree
  exact ⟨ν, r, hν, Nat.eq_of_mul_eq_mul_left hd hdeg, hshape⟩

end Dixmier.Weyl
