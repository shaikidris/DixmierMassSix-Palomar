/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.WronskianRatio
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Localization.FractionRing

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Bivariate-to-univariate derivative transport

The two-variable polynomial ring can be viewed as a polynomial ring in `x`
over the coefficient ring `ℂ[y]`. We identify partial differentiation in `x`
with the ordinary polynomial derivative under mathlib's `finSuccEquiv`.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

theorem finSuccEquiv_pderiv_zero (F : MvPolynomial (Fin 2) ℂ) :
    Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ 1 F) =
      MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.pderiv 0 F) := by
  have hX1 : MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ℂ) (n := 1) (j := 0))
  induction F using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n ih =>
      fin_cases n
      · simp [Polynomial.derivative_mul, ih, MvPolynomial.finSuccEquiv_X_zero,
          mul_comm]
      · simp [Polynomial.derivative_mul, ih, hX1, mul_comm]

/-- Polynomials in the second variable become constant polynomials in the
first variable under `finSuccEquiv`. -/
theorem finSuccEquiv_rename_succ (U : MvPolynomial (Fin 1) ℂ) :
    MvPolynomial.finSuccEquiv ℂ 1
      (MvPolynomial.rename Fin.succ U) = Polynomial.C U := by
  induction U using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n ih =>
      fin_cases n
      simp only [map_mul, MvPolynomial.rename_X, ih,
        MvPolynomial.finSuccEquiv_X_succ]

/-- Differentiation in the second variable commutes with the coefficient
embedding used by `finSuccEquiv`. -/
theorem pderiv_one_rename_succ (U : MvPolynomial (Fin 1) ℂ) :
    MvPolynomial.pderiv 1 (MvPolynomial.rename Fin.succ U) =
      MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 U) := by
  simpa using (MvPolynomial.pderiv_rename (Fin.succ_injective 1)
    (0 : Fin 1) U)

/-- The second cross-derivative annihilates a polynomial coefficient
obtained by separating the first variable. -/
theorem second_cross_derivative_forces_coefficient_derivative_zero
    (F G : MvPolynomial (Fin 2) ℂ)
    (U : MvPolynomial (Fin 1) ℂ) (hG : G ≠ 0)
    (hF : F = MvPolynomial.rename Fin.succ U * G)
    (hy : G * MvPolynomial.pderiv 1 F = F * MvPolynomial.pderiv 1 G) :
    MvPolynomial.pderiv 0 U = 0 := by
  let T := MvPolynomial.rename Fin.succ U
  rw [hF, MvPolynomial.pderiv_mul] at hy
  have hh : (G * G) * MvPolynomial.pderiv 1 T = 0 := by
    dsimp [T] at hy ⊢
    linear_combination hy
  have hT : MvPolynomial.pderiv 1 T = 0 :=
    (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hG hG)
  have hren : MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 U) = 0 := by
    simpa [T, pderiv_one_rename_succ] using hT
  exact (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective 1))
    (by simpa using hren)

/-- In the one-variable coefficient ring, the partial derivative is the
ordinary polynomial derivative under the canonical equivalence. -/
theorem uniqueAlgEquiv_pderiv_zero (U : MvPolynomial (Fin 1) ℂ) :
    Polynomial.derivative (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) U) =
      MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) (MvPolynomial.pderiv 0 U) := by
  induction U using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.uniqueAlgEquiv_apply]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p n ih =>
      have hXder : Polynomial.derivative
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) (MvPolynomial.X n)) =
          MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
            (MvPolynomial.pderiv 0 (MvPolynomial.X n)) := by
        fin_cases n
        simp [MvPolynomial.uniqueAlgEquiv_apply]
      simp only [map_mul, MvPolynomial.pderiv_mul, map_add,
        Polynomial.derivative_mul, ih, hXder]

/-- A polynomial in the one remaining variable with zero partial derivative
is a complex constant. -/
theorem finOne_eq_C_of_pderiv_zero
    (U : MvPolynomial (Fin 1) ℂ) (hU : MvPolynomial.pderiv 0 U = 0) :
    ∃ c : ℂ, U = MvPolynomial.C c := by
  let E := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  have hd : Polynomial.derivative (E U) = 0 := by
    rw [uniqueAlgEquiv_pderiv_zero, hU]
    simp
  refine ⟨(E U).coeff 0, ?_⟩
  apply E.injective
  simpa [E, MvPolynomial.uniqueAlgEquiv_apply] using
    Polynomial.eq_C_of_derivative_eq_zero hd

/-- The two cross-derivatives give an actual complex scalar once first-variable
separation has produced a polynomial coefficient in the second variable. -/
theorem polynomial_coefficient_ratio_is_complex
    (F G : MvPolynomial (Fin 2) ℂ)
    (U : MvPolynomial (Fin 1) ℂ) (hG : G ≠ 0)
    (hU : MvPolynomial.finSuccEquiv ℂ 1 F =
      Polynomial.C U * MvPolynomial.finSuccEquiv ℂ 1 G)
    (hy : G * MvPolynomial.pderiv 1 F = F * MvPolynomial.pderiv 1 G) :
    ∃ c : ℂ, F = MvPolynomial.C c * G := by
  have hF : F = MvPolynomial.rename Fin.succ U * G := by
    apply (MvPolynomial.finSuccEquiv ℂ 1).injective
    simpa only [map_mul, finSuccEquiv_rename_succ] using hU
  have hder := second_cross_derivative_forces_coefficient_derivative_zero
    F G U hG hF hy
  obtain ⟨c, hc⟩ := finOne_eq_C_of_pderiv_zero U hder
  refine ⟨c, ?_⟩
  rw [hF, hc]
  simp

/-- The `x`-direction cross-derivative identity becomes an ordinary zero
Wronskian after viewing a bivariate polynomial as a polynomial in `x`. -/
theorem finSuccEquiv_wronskian_eq_zero
    (F G : MvPolynomial (Fin 2) ℂ)
    (h : G * MvPolynomial.pderiv 0 F = F * MvPolynomial.pderiv 0 G) :
    Polynomial.wronskian (MvPolynomial.finSuccEquiv ℂ 1 F)
      (MvPolynomial.finSuccEquiv ℂ 1 G) = 0 := by
  have hm := congrArg (MvPolynomial.finSuccEquiv ℂ 1) h
  simp only [map_mul] at hm
  simp only [Polynomial.wronskian, finSuccEquiv_pderiv_zero]
  linear_combination -hm

/-- Over any characteristic-zero field containing the coefficient ring
`ℂ[y]`, the first cross-derivative identity makes the numerator a scalar
multiple of the denominator as polynomials in `x`. The scalar may still
depend rationally on `y`; the second identity must remove that dependence. -/
theorem x_cross_derivative_scalar_over_coefficient_field
    (L : Type*) [Field L] [CharZero L]
    (ι : MvPolynomial (Fin 1) ℂ →+* L) (hι : Function.Injective ι)
    (F G : MvPolynomial (Fin 2) ℂ) (hG : G ≠ 0)
    (h : G * MvPolynomial.pderiv 0 F = F * MvPolynomial.pderiv 0 G) :
    ∃ c : L,
      ((MvPolynomial.finSuccEquiv ℂ 1 F).map ι) =
        Polynomial.C c * ((MvPolynomial.finSuccEquiv ℂ 1 G).map ι) := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  have hEG : E G ≠ 0 := by
    intro hz
    apply hG
    exact E.injective (by simpa using hz)
  have hGmap : (E G).map ι ≠ 0 := by
    intro hz
    exact hEG ((Polynomial.map_injective ι hι) (by simpa using hz))
  have hW := finSuccEquiv_wronskian_eq_zero F G h
  have hWmap := congrArg (Polynomial.map ι) hW
  have hWfield : Polynomial.wronskian ((E F).map ι) ((E G).map ι) = 0 := by
    simpa [E, Polynomial.wronskian, Polynomial.derivative_map] using hWmap
  exact polynomial_wronskian_zero_scalar_ratio ((E F).map ι) ((E G).map ι)
    hGmap hWfield

/-- Specialization to the actual rational-function field in the second
variable. The scalar can depend on that second variable at this stage. -/
theorem x_cross_derivative_scalar_over_fraction_ring
    (F G : MvPolynomial (Fin 2) ℂ) (hG : G ≠ 0)
    (h : G * MvPolynomial.pderiv 0 F = F * MvPolynomial.pderiv 0 G) :
    ∃ c : FractionRing (MvPolynomial (Fin 1) ℂ),
      (MvPolynomial.finSuccEquiv ℂ 1 F).map
          (algebraMap (MvPolynomial (Fin 1) ℂ)
            (FractionRing (MvPolynomial (Fin 1) ℂ))) =
        Polynomial.C c *
          (MvPolynomial.finSuccEquiv ℂ 1 G).map
            (algebraMap (MvPolynomial (Fin 1) ℂ)
              (FractionRing (MvPolynomial (Fin 1) ℂ))) := by
  exact x_cross_derivative_scalar_over_coefficient_field
    (FractionRing (MvPolynomial (Fin 1) ℂ))
    (algebraMap (MvPolynomial (Fin 1) ℂ)
      (FractionRing (MvPolynomial (Fin 1) ℂ)))
    (IsFractionRing.injective (MvPolynomial (Fin 1) ℂ)
      (FractionRing (MvPolynomial (Fin 1) ℂ))) F G hG h

/-- If a denominator has a coefficient equal to one, a scalar ratio found
after embedding its coefficient ring in a field already comes from the
original coefficient ring. -/
theorem polynomial_scalar_ratio_descends_of_unit_coefficient
    {R L : Type*} [CommRing R] [CommRing L]
    (ι : R →+* L) (hι : Function.Injective ι)
    (f g : R[X]) (n : ℕ) (hgn : g.coeff n = 1)
    (c : L) (h : f.map ι = Polynomial.C c * g.map ι) :
    ∃ u : R, c = ι u ∧ f = Polynomial.C u * g := by
  have hc : c = ι (f.coeff n) := by
    have hn := congrArg (fun p : L[X] => p.coeff n) h
    simpa [Polynomial.coeff_map, Polynomial.coeff_C_mul, hgn] using hn.symm
  refine ⟨f.coeff n, hc, ?_⟩
  apply Polynomial.map_injective ι hι
  simpa [hc] using h

/-- A ratio over an extension field always clears to a polynomial identity
using any nonzero coefficient of the denominator. No monicity is required. -/
theorem polynomial_scalar_ratio_clears_coefficient
    {R L : Type*} [CommRing R] [CommRing L]
    (ι : R →+* L) (hι : Function.Injective ι)
    (f g : R[X]) (n : ℕ)
    (c : L) (h : f.map ι = Polynomial.C c * g.map ι) :
    Polynomial.C (g.coeff n) * f = Polynomial.C (f.coeff n) * g := by
  have hn := congrArg (fun p : L[X] => p.coeff n) h
  have hn' : ι (f.coeff n) = c * ι (g.coeff n) := by
    simpa [Polynomial.coeff_map, Polynomial.coeff_C_mul] using hn
  have hm : Polynomial.C (ι (g.coeff n)) * f.map ι =
      Polynomial.C (ι (f.coeff n)) * g.map ι := by
    calc
      _ = Polynomial.C (ι (g.coeff n)) * (Polynomial.C c * g.map ι) := by rw [h]
      _ = Polynomial.C (ι (f.coeff n)) * g.map ι := by
        rw [← mul_assoc, ← Polynomial.C_mul, mul_comm (ι (g.coeff n)) c,
          ← hn']
  apply Polynomial.map_injective ι hι
  simp only [Polynomial.map_mul, Polynomial.map_C]
  exact hm

set_option maxHeartbeats 1000000 in
/-- The first cross-derivative yields a denominator-free relation over
`ℂ[y]` even when no coefficient is a unit. The coefficient chosen is the
leading coefficient in the `x` presentation of `G`. -/
theorem bivariate_x_ratio_polynomial_relation
    (F G : MvPolynomial (Fin 2) ℂ) (hG : G ≠ 0)
    (hx : G * pderiv 0 F = F * pderiv 0 G) :
    ∃ U V : MvPolynomial (Fin 1) ℂ,
      V ≠ 0 ∧ Polynomial.C V * MvPolynomial.finSuccEquiv ℂ 1 F =
        Polynomial.C U * MvPolynomial.finSuccEquiv ℂ 1 G := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let ι : MvPolynomial (Fin 1) ℂ →+*
      FractionRing (MvPolynomial (Fin 1) ℂ) := algebraMap _ _
  have hι : Function.Injective ι :=
    IsFractionRing.injective (MvPolynomial (Fin 1) ℂ)
      (FractionRing (MvPolynomial (Fin 1) ℂ))
  have hEG : E G ≠ 0 := by
    intro hz
    exact hG (E.injective (by simpa [E] using hz))
  let V := (E G).leadingCoeff
  let U := (E F).coeff (E G).natDegree
  have hV : V ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hEG
  obtain ⟨c, hc⟩ := x_cross_derivative_scalar_over_fraction_ring F G hG hx
  have hrel : Polynomial.C V * E F = Polynomial.C U * E G :=
    polynomial_scalar_ratio_clears_coefficient ι hι (E F) (E G)
      (E G).natDegree c (by simpa [V, U, E] using hc)
  exact ⟨U, V, hV, hrel⟩

/-- Transport a cleared first-variable ratio back to the two-variable
polynomial ring. -/
theorem finSuccEquiv_cleared_ratio
    (F G : MvPolynomial (Fin 2) ℂ)
    (U V : MvPolynomial (Fin 1) ℂ)
    (h : Polynomial.C V * MvPolynomial.finSuccEquiv ℂ 1 F =
      Polynomial.C U * MvPolynomial.finSuccEquiv ℂ 1 G) :
    MvPolynomial.rename Fin.succ V * F =
      MvPolynomial.rename Fin.succ U * G := by
  apply (MvPolynomial.finSuccEquiv ℂ 1).injective
  simpa only [map_mul, finSuccEquiv_rename_succ] using h

/-- Differentiating a cleared ratio and using the second cross-derivative
identity gives a cleared ratio for the coefficient polynomials themselves. -/
theorem cleared_ratio_derivative_identity
    (F G S T : MvPolynomial (Fin 2) ℂ) (hG : G ≠ 0)
    (hrel : T * F = S * G)
    (hy : G * pderiv 1 F = F * pderiv 1 G) :
    T * pderiv 1 S = S * pderiv 1 T := by
  have hder := congrArg (pderiv 1) hrel
  simp only [MvPolynomial.pderiv_mul] at hder
  have hDmul : (pderiv 1 T * F - pderiv 1 S * G) * G = 0 := by
    linear_combination G * hder - T * hy - pderiv 1 G * hrel
  have hD : pderiv 1 T * F = pderiv 1 S * G := by
    have hz := (mul_eq_zero.mp hDmul).resolve_right hG
    exact sub_eq_zero.mp hz
  have hlast : (T * pderiv 1 S - S * pderiv 1 T) * G = 0 := by
    linear_combination pderiv 1 T * hrel - T * hD
  exact sub_eq_zero.mp ((mul_eq_zero.mp hlast).resolve_right hG)

/-- Both cross-derivative identities force a bivariate polynomial ratio to
be a complex constant. Unlike the earlier monic lemma, this has no unit
coefficient hypothesis. -/
theorem bivariate_cross_derivatives_constant
    (F G : MvPolynomial (Fin 2) ℂ) (hG : G ≠ 0)
    (hx : G * pderiv 0 F = F * pderiv 0 G)
    (hy : G * pderiv 1 F = F * pderiv 1 G) :
    ∃ c : ℂ, F = MvPolynomial.C c * G := by
  obtain ⟨U, V, hV, hUV⟩ := bivariate_x_ratio_polynomial_relation F G hG hx
  have hrel := finSuccEquiv_cleared_ratio F G U V hUV
  have hder := cleared_ratio_derivative_identity F G
    (MvPolynomial.rename Fin.succ U) (MvPolynomial.rename Fin.succ V)
    hG hrel hy
  have hUVder : V * pderiv 0 U = U * pderiv 0 V := by
    apply MvPolynomial.rename_injective Fin.succ (Fin.succ_injective 1)
    simpa only [map_mul, pderiv_one_rename_succ] using hder
  let E := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  have hEV : E V ≠ 0 := fun hz => hV (E.injective (by simpa [E] using hz))
  have hW : Polynomial.wronskian (E U) (E V) = 0 := by
    have hm := congrArg E hUVder
    simp only [map_mul] at hm
    have hdU : Polynomial.derivative (E U) = E (pderiv 0 U) :=
      uniqueAlgEquiv_pderiv_zero U
    have hdV : Polynomial.derivative (E V) = E (pderiv 0 V) :=
      uniqueAlgEquiv_pderiv_zero V
    simp only [Polynomial.wronskian, hdU, hdV]
    linear_combination -hm
  obtain ⟨c, hc⟩ := polynomial_wronskian_zero_scalar_ratio (E U) (E V) hEV hW
  have hU : U = MvPolynomial.C c * V := by
    apply E.injective
    simpa [E, MvPolynomial.uniqueAlgEquiv_apply] using hc
  refine ⟨c, ?_⟩
  rw [hU] at hrel
  have hVren : MvPolynomial.rename Fin.succ V ≠ 0 := by
    intro hz
    exact hV (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective 1) hz)
  have hcancel : MvPolynomial.rename Fin.succ V * F =
      MvPolynomial.rename Fin.succ V * (MvPolynomial.C c * G) := by
    simpa [map_mul, mul_assoc, mul_comm, mul_left_comm] using hrel
  exact mul_left_cancel₀ hVren hcancel

/-- A monic coefficient in the first-variable presentation lets the two
cleared logarithmic-derivative identities descend from the rational
coefficient field to an actual complex proportionality. This is a general
bivariate factor-ratio lemma, independent of the strict crossing shape. -/
theorem bivariate_cross_derivatives_constant_of_monic_x
    (F G : MvPolynomial (Fin 2) ℂ) (n : ℕ)
    (hmonic : (MvPolynomial.finSuccEquiv ℂ 1 G).coeff n = 1)
    (hx : G * pderiv 0 F = F * pderiv 0 G)
    (hy : G * pderiv 1 F = F * pderiv 1 G) :
    ∃ c : ℂ, F = MvPolynomial.C c * G := by
  let ι : MvPolynomial (Fin 1) ℂ →+*
      FractionRing (MvPolynomial (Fin 1) ℂ) := algebraMap _ _
  have hι : Function.Injective ι :=
    IsFractionRing.injective (MvPolynomial (Fin 1) ℂ)
      (FractionRing (MvPolynomial (Fin 1) ℂ))
  have hG : G ≠ 0 := by
    intro hzero
    simp [hzero] at hmonic
  obtain ⟨c, hc⟩ := x_cross_derivative_scalar_over_fraction_ring F G hG hx
  obtain ⟨u, _, hu⟩ := polynomial_scalar_ratio_descends_of_unit_coefficient
    ι hι (MvPolynomial.finSuccEquiv ℂ 1 F)
      (MvPolynomial.finSuccEquiv ℂ 1 G) n hmonic c hc
  exact polynomial_coefficient_ratio_is_complex F G u hG hu hy

/-- For a strict crossing (`s > 0`), the coefficient at the lowest
`x`-power of the paper's face power is exactly one. -/
theorem crossingBase_power_lowest_x_coefficient
    (α : ℂ) (q ρ s ω : ℕ) (hs : 0 < s) :
    ((MvPolynomial.finSuccEquiv ℂ 1)
      ((MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω)).coeff ω = 1 := by
  have hX1 : MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ℂ) (n := 1) (j := 0))
  simp only [map_pow, map_mul, map_add, map_one, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, hX1]
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rw [mul_pow, ← pow_mul]
  have hcoeff (p : Polynomial (MvPolynomial (Fin 1) ℂ)) :
      (Polynomial.X ^ ω * p).coeff ω = p.coeff 0 := by
    simpa using (Polynomial.coeff_X_pow_mul p ω 0)
  rw [hcoeff]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [hs.ne']

/-- For a strict crossing, the first logarithmic-derivative equation already
gives a polynomial, rather than merely rational, scalar in the other variable.
This remains a one-direction statement: the second derivative must show the
scalar is constant. -/
theorem crossingBase_power_x_ratio_polynomial
    (F : MvPolynomial (Fin 2) ℂ) (α : ℂ) (q ρ s ω : ℕ)
    (hs : 0 < s)
    (h : (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ ω * MvPolynomial.pderiv 0 F =
        F * MvPolynomial.pderiv 0
          ((MvPolynomial.X 0 *
            (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) ^ ω)) :
    ∃ U : MvPolynomial (Fin 1) ℂ,
      MvPolynomial.finSuccEquiv ℂ 1 F =
        Polynomial.C U * MvPolynomial.finSuccEquiv ℂ 1
          ((MvPolynomial.X 0 *
            (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) ^ ω) := by
  let G : MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
        MvPolynomial.X 1 ^ ρ) ^ q) ^ ω
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let ι := algebraMap (MvPolynomial (Fin 1) ℂ)
    (FractionRing (MvPolynomial (Fin 1) ℂ))
  have hgn : (E G).coeff ω = 1 :=
    crossingBase_power_lowest_x_coefficient α q ρ s ω hs
  have hG : G ≠ 0 := by
    intro hz
    have : (E G).coeff ω = 0 := by simp [hz]
    exact one_ne_zero (hgn.symm.trans this)
  obtain ⟨c, hc⟩ := x_cross_derivative_scalar_over_fraction_ring F G hG h
  obtain ⟨U, -, hU⟩ :=
    polynomial_scalar_ratio_descends_of_unit_coefficient ι
      (IsFractionRing.injective (MvPolynomial (Fin 1) ℂ)
        (FractionRing (MvPolynomial (Fin 1) ℂ))) (E F) (E G) ω hgn c hc
  exact ⟨U, hU⟩

/-- For the strict-crossing face, both cleared derivative identities imply
constant proportionality in the polynomial ring itself. This is the
denominator-free form of the paper's rational-function assertion. -/
theorem crossingBase_power_cross_derivatives_constant
    (F : MvPolynomial (Fin 2) ℂ) (α : ℂ) (q ρ s ω : ℕ)
    (hs : 0 < s)
    (hx : (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ ω * MvPolynomial.pderiv 0 F =
        F * MvPolynomial.pderiv 0
          ((MvPolynomial.X 0 *
            (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) ^ ω))
    (hy : (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ ω * MvPolynomial.pderiv 1 F =
        F * MvPolynomial.pderiv 1
          ((MvPolynomial.X 0 *
            (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
              MvPolynomial.X 1 ^ ρ) ^ q) ^ ω)) :
    ∃ c : ℂ, F = MvPolynomial.C c *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ ω := by
  let G : MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
        MvPolynomial.X 1 ^ ρ) ^ q) ^ ω
  have hgn : ((MvPolynomial.finSuccEquiv ℂ 1) G).coeff ω = 1 :=
    crossingBase_power_lowest_x_coefficient α q ρ s ω hs
  have hG : G ≠ 0 := by
    intro hz
    have : ((MvPolynomial.finSuccEquiv ℂ 1) G).coeff ω = 0 := by simp [hz]
    exact one_ne_zero (hgn.symm.trans this)
  obtain ⟨U, hU⟩ := crossingBase_power_x_ratio_polynomial F α q ρ s ω hs hx
  exact polynomial_coefficient_ratio_is_complex F G U hG hU hy

/-- The actual Weyl mate on a strict crossing face satisfies the constant
power-ratio identity. The horizontal case `s = 0` is handled separately in
the paper and is not claimed by this theorem. -/
theorem crossingFace_mate_power_ratio_constant
    (P Q : A1 ℂ) (μ α : ℂ) (p q ρ s ω : ℕ)
    (hμ : μ ≠ 0) (hp : 2 ≤ p) (hs : 0 < s) (hsρ : s < ρ) (hω : 0 < ω)
    (hexact : Q * P - P * Q = 1)
    (hPweight : vDeg ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X]) = ω)
    (hPface : leadingForm ρ (-(s : ℤ)) (P : Module.End ℂ ℂ[X]) =
      MvPolynomial.C μ *
        (X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q) ^ p) :
    let R : MvPolynomial (Fin 2) ℂ :=
      X 0 * (1 + MvPolynomial.C α * X 0 ^ s * X 1 ^ ρ) ^ q
    let B := leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])
    ∃ c : ℂ, B ^ ρ = MvPolynomial.C c * R ^ ω := by
  dsimp
  obtain ⟨hx, hy⟩ := crossingFace_mate_power_cross_derivatives
    P Q μ α p q ρ s ω hμ hp hsρ hω hexact hPweight hQweight hPface
  exact crossingBase_power_cross_derivatives_constant
    ((leadingForm ρ (-(s : ℤ)) (Q : Module.End ℂ ℂ[X])) ^ ρ)
    α q ρ s ω hs hx hy

end Dixmier.Weyl
