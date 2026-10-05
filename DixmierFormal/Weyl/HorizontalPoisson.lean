/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/

module

public import DixmierFormal.Weyl.HorizontalFace
public import DixmierFormal.Weyl.PoissonSubstitution
public import DixmierFormal.Scalar.HorizontalCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal Poisson companion equation

For displayed horizontal face and companion shapes, this file computes the
bivariate Poisson bracket and transports it to the ordinary polynomial
companion equation. Extracting those shapes from GGVInputs is separate.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

private theorem pderiv_zero_rename_succ (U : MvPolynomial (Fin 1) ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.rename Fin.succ U) = 0 := by
  induction U using MvPolynomial.induction_on with
  | C c => simp
  | add U V hU hV => simp [hU, hV]
  | mul_X U i ih =>
      fin_cases i
      simp [map_mul, MvPolynomial.rename_X, ih]

theorem horizontal_poisson_formula (G F : MvPolynomial (Fin 1) ℂ) (a : ℕ) :
    poisson (MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ G)
      (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ F) =
    MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ
      (F * MvPolynomial.pderiv 0 G -
        MvPolynomial.C (a : ℂ) * G * MvPolynomial.pderiv 0 F) := by
  let x : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0
  let Ug := MvPolynomial.rename Fin.succ G
  let Uf := MvPolynomial.rename Fin.succ F
  have hx : x ≠ 0 := by simp [x]
  have hRg_y : MvPolynomial.pderiv 1 (x ^ a * Ug) =
      x ^ a * MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 G) := by
    dsimp [x, Ug]
    rw [MvPolynomial.pderiv_mul]
    simp [pderiv_one_rename_succ]
  have hRf_y : MvPolynomial.pderiv 1 (x * Uf) =
      x * MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 F) := by
    dsimp [x, Uf]
    rw [MvPolynomial.pderiv_mul]
    simp [pderiv_one_rename_succ]
  have hRg_x : x * MvPolynomial.pderiv 0 (x ^ a * Ug) =
      MvPolynomial.C (a : ℂ) * (x ^ a * Ug) := by
    dsimp [Ug]
    rw [MvPolynomial.pderiv_mul, pderiv_zero_rename_succ]
    simp only [mul_zero, add_zero]
    have he := euler_X_pow 0 a
    dsimp [x]
    calc
      MvPolynomial.X 0 *
          (MvPolynomial.pderiv 0 (MvPolynomial.X 0 ^ a) *
            MvPolynomial.rename Fin.succ G) =
          (MvPolynomial.X 0 * MvPolynomial.pderiv 0 (MvPolynomial.X 0 ^ a)) *
            MvPolynomial.rename Fin.succ G := by ring
      _ = _ := by rw [he]; ring
  have hRf_x : x * MvPolynomial.pderiv 0 (x * Uf) = x * Uf := by
    dsimp [x, Uf]
    rw [MvPolynomial.pderiv_mul, pderiv_zero_rename_succ]
    simp
  apply mul_left_cancel₀ hx
  have hprod : x * poisson (x ^ a * Ug) (x * Uf) =
      (x ^ a * MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 G)) *
          (x * Uf) -
        (MvPolynomial.C (a : ℂ) * (x ^ a * Ug)) *
          (x * MvPolynomial.rename Fin.succ (MvPolynomial.pderiv 0 F)) := by
    calc
      x * poisson (x ^ a * Ug) (x * Uf) =
          MvPolynomial.pderiv 1 (x ^ a * Ug) *
            (x * MvPolynomial.pderiv 0 (x * Uf)) -
          (x * MvPolynomial.pderiv 0 (x ^ a * Ug)) *
            MvPolynomial.pderiv 1 (x * Uf) := by unfold poisson; ring
      _ = _ := by rw [hRg_y, hRf_x, hRg_x, hRf_y]
  dsimp [x, Ug, Uf] at hprod ⊢
  rw [hprod]
  simp only [map_sub, map_mul, MvPolynomial.rename_C]
  ring

theorem horizontal_poisson_implies_scalar (G F : MvPolynomial (Fin 1) ℂ) (a : ℕ)
    (hpoisson : poisson
      (MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ G)
      (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ F) =
      MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ G) :
    Dixmier.Horizontal.HorizComp a
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) G)
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) F) := by
  have hcancel : MvPolynomial.rename Fin.succ
      (F * MvPolynomial.pderiv 0 G -
        MvPolynomial.C (a : ℂ) * G * MvPolynomial.pderiv 0 F) =
      MvPolynomial.rename Fin.succ G := by
    apply mul_left_cancel₀ (pow_ne_zero a (by simp :
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ≠ 0))
    rw [← horizontal_poisson_formula]
    exact hpoisson
  have hsmall := (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective 1))
    hcancel
  let E := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  have hmap := congrArg E hsmall
  simp only [map_sub, map_mul] at hmap
  dsimp [E] at hmap
  rw [← uniqueAlgEquiv_pderiv_zero G,
    ← uniqueAlgEquiv_pderiv_zero F] at hmap
  have hC : (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
      (MvPolynomial.C (a : ℂ)) = Polynomial.C (a : ℂ) := by simp
  rw [hC] at hmap
  unfold Dixmier.Horizontal.HorizComp
  convert hmap using 1
  ring

end Dixmier.Weyl
