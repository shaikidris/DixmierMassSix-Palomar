/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalWronskian

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
/-!
# Horizontal mate power from the exact Weyl relation

At the parameter boundary `(q,ρ,s)=(2,1,0)`, the positive horizontal mate
face separates as `x^ω U(y)`. The exact commutator supplies a cross-derivative
identity, and the one-variable Wronskian theorem forces the coefficient to be
a scalar multiple of `(1+αy)^(2ω)`. No mate-order or mass bound is used.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Rewrite a horizontal primitive-base power using the coefficient ring
`ℂ[y]` under `finSuccEquiv`. -/
theorem horizontal_base_power_shape (α : ℂ) (ω : ℕ) :
    (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
        MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ ω =
      MvPolynomial.X 0 ^ ω * MvPolynomial.rename Fin.succ
        ((1 + MvPolynomial.C α * MvPolynomial.X 0) ^ (2 * ω) :
          MvPolynomial (Fin 1) ℂ) := by
  simp only [pow_zero, pow_one]
  rw [mul_pow, ← pow_mul]
  simp only [map_pow, map_add, map_one, map_mul, MvPolynomial.rename_X,
    MvPolynomial.rename_C]
  simp [mul_comm]

/-- The actual exact Weyl mate has a positive integer horizontal face
exponent and the same primitive base as `P`, conditional on the published
opposite-grade input used to keep its weight positive. -/
theorem horizontal_mate_is_base_power
    (H : GGVInputs) (P Q : A1 ℂ) (α μ : ℂ) (p : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p)
    (hPface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ p)
    (hpair : IsCounterexamplePair P Q) :
    ∃ (j : ℕ) (ν : ℂ), 0 < j ∧ ν ≠ 0 ∧
      vDeg 1 0 Q.1 = j ∧
      leadingForm 1 0 Q.1 = MvPolynomial.C ν *
        (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
            MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j := by
  have hPweight : vDeg 1 0 P.1 = (p : ℤ) := by
    simpa using crossingFace_weight_any_s P α μ 2 1 0 p hμ (by decide) hPface
  have hQpos : 0 < vDeg 1 0 Q.1 :=
    counterexample_mate_weight_pos H P Q hpair 1 0 (by decide)
  obtain ⟨ω, U, hω, hQweight, hQface⟩ := horizontal_operator_face_shape Q hQpos
  have hPweight' : vDeg (1 : ℤ) (-(0 : ℤ)) P.1 = (p : ℤ) * 1 := by
    simpa using hPweight
  have hQweight' : vDeg (1 : ℤ) (-(0 : ℤ)) Q.1 = (ω : ℤ) := by
    simpa using hQweight
  let V : MvPolynomial (Fin 1) ℂ :=
    (1 + MvPolynomial.C α * MvPolynomial.X 0) ^ (2 * ω)
  have hbase : (1 + MvPolynomial.C α * MvPolynomial.X 0 :
      MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    intro hz
    have heval := congrArg (MvPolynomial.eval fun _ : Fin 1 => (0 : ℂ)) hz
    simp at heval
  have hV : V ≠ 0 := pow_ne_zero _ hbase
  obtain ⟨_, hy⟩ := crossingFace_mate_power_cross_derivatives
    P Q μ α p 2 1 0 ω hμ hp (by decide) hω hpair.1
      hPweight' hQweight' hPface
  simp only [pow_one] at hy
  have hRshape := horizontal_base_power_shape α ω
  simp only [pow_zero, pow_one] at hy hRshape
  simp only [Nat.cast_one, Nat.cast_zero, neg_zero] at hy
  rw [hQface, hRshape] at hy
  obtain ⟨ν, hU⟩ := horizontal_cross_derivative_scalar_ratio U V ω hV hy
  have hν : ν ≠ 0 := by
    intro hz
    have hzero : leadingForm 1 0 Q.1 = 0 := by
      rw [hQface, hU, hz]
      simp
    exact (leadingForm_ne_zero_of_vDeg_pos Q 1 0 hQpos) hzero
  refine ⟨ω, ν, hω, hν, hQweight, ?_⟩
  rw [hQface, hU]
  have hR := horizontal_base_power_shape α ω
  rw [hR]
  simp only [map_mul, MvPolynomial.rename_C]
  ring

end Dixmier.Weyl
