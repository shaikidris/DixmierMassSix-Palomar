/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedLeadingPoissonZero
public import DixmierFormal.Weyl.WronskianRatio
public import DixmierFormal.Scalar.Section6Roots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Power and root-order ratios on the ramified top faces

Positive-weight bracket vanishing gives a scalar power identity and
root-multiplicity alignment for unrestricted exact ramified pairs.
-/

namespace Dixmier.Weyl

/-- A zero weighted derivative bracket gives a scalar power ratio for
two nonzero complex polynomials at positive integer weights. -/
theorem polynomial_power_ratio_of_weighted_derivative_zero
    (f g : Polynomial ℂ) (A D : ℕ)
    (hA : 0 < A) (hD : 0 < D)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hbr : Polynomial.C (D : ℂ) * (f.derivative * g) -
      Polynomial.C (A : ℂ) * (f * g.derivative) = 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      f ^ D = Polynomial.C c * g ^ A := by
  have hw : Polynomial.wronskian (f^D) (g^A) = 0 := by
    cases A with
    | zero => omega
    | succ a =>
      cases D with
      | zero => omega
      | succ d =>
        rw [Polynomial.wronskian,
          Polynomial.derivative_pow_succ,
          Polynomial.derivative_pow_succ,
          pow_succ f d, pow_succ g a]
        simp only [Nat.cast_add, Nat.cast_one] at hbr ⊢
        linear_combination -(f^d*g^a)*hbr
  obtain ⟨c,hc⟩ := polynomial_wronskian_zero_scalar_ratio
    (f^D) (g^A) (pow_ne_zero _ hg) hw
  refine ⟨c, ?_, hc⟩
  intro hz
  have hzero : f^D = 0 := by simpa [hz] using hc
  exact (pow_ne_zero _ hf) hzero

/-- Clear the nonzero ramification and horizontal-weight denominator in
a polynomial derivative bracket. -/
theorem polynomial_weighted_derivative_clear_denominator
    (f g : Polynomial ℂ) (A D : ℂ) (den : ℂ)
    (hden : den ≠ 0)
    (h : Polynomial.C (D/den) * (f.derivative*g) -
      Polynomial.C (A/den) * (f*g.derivative) = 0) :
    Polynomial.C D * (f.derivative*g) -
      Polynomial.C A * (f*g.derivative) = 0 := by
  have hmul := congrArg (fun t : Polynomial ℂ => Polynomial.C den * t) h
  simp only [mul_sub, mul_zero] at hmul
  have hD : Polynomial.C den * Polynomial.C (D/den) =
      Polynomial.C D := by
    rw [← map_mul]
    field_simp
  have hA : Polynomial.C den * Polynomial.C (A/den) =
      Polynomial.C A := by
    rw [← map_mul]
    field_simp
  simpa only [← mul_assoc,hD,hA] using hmul

/-- Coprime reduced face weights force the denominator to divide every root
multiplicity of the first face. This precedes common-base extraction. -/
theorem rootMultiplicity_dvd_of_coprime_power_ratio
    (f g : Polynomial ℂ) (A D n d : ℕ)
    (hA : 0 < A) (hratio : D * d = A * n)
    (hcop : Nat.Coprime d n)
    (hroots : ∀ a : ℂ,
      D * f.rootMultiplicity a = A * g.rootMultiplicity a)
    (a : ℂ) : d ∣ f.rootMultiplicity a := by
  have heq : A * (n * f.rootMultiplicity a) =
      A * (d * g.rootMultiplicity a) := by
    calc
      A * (n * f.rootMultiplicity a) = (D * d) * f.rootMultiplicity a := by
        rw [hratio]
        ac_rfl
      _ = d * (D * f.rootMultiplicity a) := by ac_rfl
      _ = d * (A * g.rootMultiplicity a) := by rw [hroots]
      _ = A * (d * g.rootMultiplicity a) := by ac_rfl
  have hcancel : n * f.rootMultiplicity a =
      d * g.rootMultiplicity a := by
    exact Nat.eq_of_mul_eq_mul_left hA heq
  apply hcop.dvd_of_dvd_mul_left
  rw [hcancel]
  exact dvd_mul_right d (g.rootMultiplicity a)

/-- The two actual ramified top faces of an exact pair have the
expected scalar power ratio when both face weights and the first
contraction threshold are positive. -/
theorem ramified_exact_pair_top_face_power_ratio
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ)) :
    ∃ c : ℂ, c ≠ 0 ∧
      (ramifiedTopFacePolynomial l hl ρ σ P) ^
        (ramifiedWeightDeg l hl ρ σ Q).toNat =
        Polynomial.C c *
          (ramifiedTopFacePolynomial l hl ρ σ Q) ^
            (ramifiedWeightDeg l hl ρ σ P).toNat := by
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  let g := ramifiedTopFacePolynomial l hl ρ σ Q
  let A := ramifiedWeightDeg l hl ρ σ P
  let D := ramifiedWeightDeg l hl ρ σ Q
  have hf : f ≠ 0 := ramifiedTopFacePolynomial_ne_zero
    l hl ρ σ hρ P hPne
  have hg : g ≠ 0 := ramifiedTopFacePolynomial_ne_zero
    l hl ρ σ hρ Q hQne
  have hbr := ramified_exact_pair_top_face_bracket_eq_zero
    l hl ρ σ hρ hsum P Q hPne hQne hcomm hthreshold
  change Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f.derivative*g) -
    Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f*g.derivative) = 0 at hbr
  have hden : (l : ℂ)*(ρ : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hl)
      (by exact_mod_cast ne_of_gt hρ)
  have hclear := polynomial_weighted_derivative_clear_denominator
    f g (A : ℂ) (D : ℂ) ((l : ℂ)*(ρ : ℂ)) hden hbr
  have hAcast : ((A.toNat : ℕ) : ℂ) = (A : ℂ) := by
    dsimp [A]
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hA)
  have hDcast : ((D.toNat : ℕ) : ℂ) = (D : ℂ) := by
    dsimp [D]
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hD)
  have hAPos : 0 < A.toNat := by
    have := Int.toNat_of_nonneg (le_of_lt hA)
    omega
  have hDPos : 0 < D.toNat := by
    have := Int.toNat_of_nonneg (le_of_lt hD)
    omega
  have hclearNat : Polynomial.C ((D.toNat : ℕ) : ℂ) *
      (f.derivative*g) -
    Polynomial.C ((A.toNat : ℕ) : ℂ) *
      (f*g.derivative) = 0 := by
    simpa only [hAcast,hDcast] using hclear
  exact polynomial_power_ratio_of_weighted_derivative_zero
    f g A.toNat D.toNat hAPos hDPos hf hg hclearNat

/-- Every complex root of the two actual ramified top faces has
proportional multiplicities, including a selected maximum-cut root. -/
theorem ramified_exact_pair_top_face_rootMultiplicity_ratio
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ))
    (a : ℂ) :
    (ramifiedWeightDeg l hl ρ σ Q).toNat *
        (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity a =
      (ramifiedWeightDeg l hl ρ σ P).toNat *
        (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity a := by
  obtain ⟨c,hc,hpow⟩ := ramified_exact_pair_top_face_power_ratio
    l hl ρ σ hρ hsum P Q hPne hQne hcomm hA hD hthreshold
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hPne
  have hg := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ Q hQne
  have h := congrArg (Polynomial.rootMultiplicity a) hpow
  rw [Dixmier.section6_rootMultiplicity_pow,
    Polynomial.rootMultiplicity_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
        (pow_ne_zero _ hg)),
    Polynomial.rootMultiplicity_C,
    zero_add,
    Dixmier.section6_rootMultiplicity_pow] at h
  exact h

/-- For an exact ramified pair whose positive face-weight ratio is reduced as
`n/d`, each root multiplicity of the first actual top face is divisible by
`d`. No degree or support bound is imposed on the mate. -/
theorem ramified_exact_pair_top_face_rootMultiplicity_dvd
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
    (hcop : Nat.Coprime d n) (a : ℂ) :
    d ∣ (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity a := by
  have hAPos : 0 < (ramifiedWeightDeg l hl ρ σ P).toNat := by
    omega
  apply rootMultiplicity_dvd_of_coprime_power_ratio
    (ramifiedTopFacePolynomial l hl ρ σ P)
    (ramifiedTopFacePolynomial l hl ρ σ Q)
    (ramifiedWeightDeg l hl ρ σ P).toNat
    (ramifiedWeightDeg l hl ρ σ Q).toNat
    n d hAPos hratio hcop
    (fun z => ramified_exact_pair_top_face_rootMultiplicity_ratio
      l hl ρ σ hρ hsum P Q hPne hQne hcomm hA hD hthreshold z) a

end Dixmier.Weyl
