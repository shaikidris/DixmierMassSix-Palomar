/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FaceCutMass
public import DixmierFormal.Scalar.SparseRoots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The two-root total-degree face: scalar cut and sparse multiplicity

These lemmas identify the exact one-variable cut of the remaining GGV
total-degree alternative and apply the already-proved sparse-root theorem.
The degree comparison and final mass contradiction are separate obligations.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem twoRoot_cutPoly
    (T : A1 ℂ) (lam α β : ℂ) (u v : ℕ)
    (hface : leadingForm 1 1 T.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0) ^ u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0) ^ v) :
    cutPoly 1 1 T.1 = Polynomial.C lam *
      (Polynomial.X - Polynomial.C α) ^ u *
      (Polynomial.X - Polynomial.C β) ^ v := by
  rw [cutPoly, hface]
  let φ := MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then (1 : ℂ[X]) else Polynomial.X)
  change φ (MvPolynomial.C lam *
    (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0) ^ u *
    (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0) ^ v) = _
  simp only [map_mul, map_pow, map_sub]
  dsimp [φ]
  simp only [MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  norm_num

theorem twoRoot_cutPoly_termCount_gt_exponents
    (T : A1 ℂ) (lam α β : ℂ) (u v : ℕ)
    (hlam : lam ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hface : leadingForm 1 1 T.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0) ^ u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0) ^ v) :
    u < termCount (cutPoly 1 1 T.1) ∧
      v < termCount (cutPoly 1 1 T.1) := by
  let S : ℂ[X] := Polynomial.C lam *
    (Polynomial.X - Polynomial.C α) ^ u *
    (Polynomial.X - Polynomial.C β) ^ v
  have hS : S ≠ 0 := by
    dsimp [S]
    exact mul_ne_zero
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hlam)
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero β))
  have hcut : cutPoly 1 1 T.1 = S := twoRoot_cutPoly T lam α β u v hface
  have hαdvd : (Polynomial.X - Polynomial.C α) ^ u ∣ S := by
    dsimp [S]
    refine ⟨Polynomial.C lam * (Polynomial.X - Polynomial.C β) ^ v, ?_⟩
    ring
  have hβdvd : (Polynomial.X - Polynomial.C β) ^ v ∣ S := by
    dsimp [S]
    refine ⟨Polynomial.C lam * (Polynomial.X - Polynomial.C α) ^ u, ?_⟩
    ring
  rw [hcut]
  exact ⟨Dixmier.pow_dvd_imp_lt_termCount hS hα hαdvd,
    Dixmier.pow_dvd_imp_lt_termCount hS hβ hβdvd⟩

end Dixmier.Weyl
