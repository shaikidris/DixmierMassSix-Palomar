/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FaceCancellation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Leading forms of Weyl powers

The exact Weyl product law propagates the top face through every positive
power. This is the operator-side bridge needed before choosing a mate
subtraction coefficient in the pure-power descent.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

theorem leadingForm_pow_succ (P : A1 K) (ρ σ m : ℤ)
    (hpos : 0 < ρ + σ)
    (hPdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (n : ℕ) :
    weightedTotalDegree' (wt ρ σ)
      (symbol ((P ^ (n + 1) : A1 K) : Module.End K K[X])) =
        (((n + 1 : ℕ) : ℤ) * m : WithBot ℤ) ∧
    leadingForm ρ σ ((P ^ (n + 1) : A1 K) : Module.End K K[X]) =
      (leadingForm ρ σ (P : Module.End K K[X])) ^ (n + 1) := by
  induction n with
  | zero =>
      simpa using And.intro hPdeg (rfl : leadingForm ρ σ (P : Module.End K K[X]) =
        leadingForm ρ σ (P : Module.End K K[X]))
  | succ n ih =>
      have hmul := symbol_mul_degree_and_leadingForm (P ^ (n + 1)) P ρ σ
        (((n + 1 : ℕ) : ℤ) * m) m hpos ih.1 hPdeg
      constructor
      · rw [pow_succ]
        have harith : (((n + 1 : ℕ) : ℤ) * m) + m =
            (((n + 1 + 1 : ℕ) : ℤ) * m) := by push_cast; ring
        have hcast : ((((n + 1 : ℕ) : ℤ) * m : ℤ) : WithBot ℤ) + (m : WithBot ℤ) =
            ((((n + 1 + 1 : ℕ) : ℤ) * m : ℤ) : WithBot ℤ) := by
          rw [← WithBot.coe_add, harith]
        rw [hcast] at hmul
        exact hmul.1
      · rw [pow_succ]
        rw [hmul.2, ih.2, ← pow_succ]

/-- Nonzero scalar multiplication preserves exact weighted degree and scales
the leading form, with no assumption on the sign of the weight. -/
theorem leadingForm_smul (P : A1 K) (c : K) (hc : c ≠ 0)
    (ρ σ m : ℤ)
    (hPdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ)) :
    weightedTotalDegree' (wt ρ σ)
      (symbol ((c • P : A1 K) : Module.End K K[X])) = (m : WithBot ℤ) ∧
    leadingForm ρ σ ((c • P : A1 K) : Module.End K K[X]) =
      c • leadingForm ρ σ (P : Module.End K K[X]) := by
  have hsym := symbol_smul c P
  have hdeg : weightedTotalDegree' (wt ρ σ)
      (symbol ((c • P : A1 K) : Module.End K K[X])) = (m : WithBot ℤ) := by
    rw [hsym]
    simpa only [weightedTotalDegree', MvPolynomial.support_smul_eq hc] using hPdeg
  have hvP : vDeg ρ σ (P : Module.End K K[X]) = m := by
    simp [vDeg, hPdeg]
  have hvTerm : vDeg ρ σ ((c • P : A1 K) : Module.End K K[X]) = m := by
    change WithBot.unbotD 0
      (weightedTotalDegree' (wt ρ σ)
        (symbol ((c • P : A1 K) : Module.End K K[X]))) = m
    rw [hdeg]
    rfl
  refine ⟨hdeg, ?_⟩
  simp only [leadingForm, hvP, hvTerm]
  rw [hsym, map_smul]

/-- If the mate's top face equals a nonzero scalar times a positive power of
`P`'s top face, the paper's exact subtraction lowers its positive weight.
The theorem does not assert that such a scalar/power is always available. -/
theorem mateSubtraction_weight_drop_of_power_face (P Q : A1 K) (c : K) (hc : c ≠ 0)
    (n : ℕ) (ρ σ m : ℤ) (hpos : 0 < ρ + σ)
    (hweight : 0 < ((n + 1 : ℕ) : ℤ) * m)
    (hPdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) =
        (((n + 1 : ℕ) : ℤ) * m : WithBot ℤ))
    (hface : leadingForm ρ σ (Q : Module.End K K[X]) =
      c • (leadingForm ρ σ (P : Module.End K K[X])) ^ (n + 1)) :
    vDeg ρ σ ((Q - c • P ^ (n + 1) : A1 K) : Module.End K K[X]) <
      ((n + 1 : ℕ) : ℤ) * m := by
  have hpow := leadingForm_pow_succ P ρ σ m hpos hPdeg n
  have hscalar := leadingForm_smul (P ^ (n + 1)) c hc ρ σ
    (((n + 1 : ℕ) : ℤ) * m) hpow.1
  have htermFace : leadingForm ρ σ
      ((c • P ^ (n + 1) : A1 K) : Module.End K K[X]) =
      c • (leadingForm ρ σ (P : Module.End K K[X])) ^ (n + 1) := by
    rw [hscalar.2, hpow.2]
  have hform : leadingForm ρ σ (Q : Module.End K K[X]) =
      leadingForm ρ σ ((c • P ^ (n + 1) : A1 K) : Module.End K K[X]) := by
    rw [htermFace]
    exact hface
  exact mateSubtraction_weight_drop_of_leadingForm_eq P Q c (n + 1) ρ σ
    (((n + 1 : ℕ) : ℤ) * m) hweight hQdeg hscalar.1 hform

omit [CharZero K] in
/-- The explicit coefficient used in pure-power mate descent. When `j=p*k`,
the face `ν R^j` is a scalar multiple of the `k`-th power of `μ R^p`.
This is a commutative-symbol identity, prior to any Weyl subtraction. -/
theorem purePower_face_scalar_cancellation (R : MvPolynomial (Fin 2) K)
    (μ ν : K) (hμ : μ ≠ 0) (p k : ℕ) :
    MvPolynomial.C ν * R ^ (p * k) =
      (ν * (μ ^ k)⁻¹) • (MvPolynomial.C μ * R ^ p) ^ k := by
  rw [MvPolynomial.smul_eq_C_mul]
  rw [mul_pow, ← map_pow, pow_mul]
  have hμk : μ ^ k ≠ 0 := pow_ne_zero _ hμ
  have hscalar : (ν * (μ ^ k)⁻¹) * μ ^ k = ν := by field_simp [hμk]
  rw [← mul_assoc, ← MvPolynomial.C_mul, hscalar]

/-- An explicitly identified pure-power leading mate face supplies the actual
Weyl subtraction coefficient and a strict decrease in positive weight. -/
theorem mateSubtraction_weight_drop_of_purePower_faces
    (P Q : A1 K) (R : MvPolynomial (Fin 2) K)
    (μ ν : K) (hμ : μ ≠ 0) (hν : ν ≠ 0) (p n : ℕ)
    (ρ σ m : ℤ) (hpos : 0 < ρ + σ)
    (hweight : 0 < ((n + 1 : ℕ) : ℤ) * m)
    (hPdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (P : Module.End K K[X])) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) =
        (((n + 1 : ℕ) : ℤ) * m : WithBot ℤ))
    (hPface : leadingForm ρ σ (P : Module.End K K[X]) =
      MvPolynomial.C μ * R ^ p)
    (hQface : leadingForm ρ σ (Q : Module.End K K[X]) =
      MvPolynomial.C ν * R ^ (p * (n + 1))) :
    vDeg ρ σ
      ((Q - (ν * (μ ^ (n + 1))⁻¹) • P ^ (n + 1) : A1 K) : Module.End K K[X]) <
        ((n + 1 : ℕ) : ℤ) * m := by
  have hc : ν * (μ ^ (n + 1))⁻¹ ≠ 0 :=
    mul_ne_zero hν (inv_ne_zero (pow_ne_zero _ hμ))
  have hface : leadingForm ρ σ (Q : Module.End K K[X]) =
      (ν * (μ ^ (n + 1))⁻¹) •
        (leadingForm ρ σ (P : Module.End K K[X])) ^ (n + 1) := by
    rw [hQface, hPface]
    exact purePower_face_scalar_cancellation R μ ν hμ p (n + 1)
  exact mateSubtraction_weight_drop_of_power_face P Q _ hc n ρ σ m
    hpos hweight hPdeg hQdeg hface

end Dixmier.Weyl
