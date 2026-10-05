/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingTermCount

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Weight of a general normalized crossing face

Every term of `r(x^s y^ρ)` has signed weight zero. A nonzero powered
face therefore determines the old leading weight without a separate
numerical assumption.
-/

namespace Dixmier.Weyl
open Polynomial MvPolynomial

theorem crossing_general_scalar_substitution_homogeneous
    (r : ℂ[X]) (ρ s : ℕ) :
    (r.eval₂ MvPolynomial.C
      (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)).IsWeightedHomogeneous
        (wt ρ (-(s : ℤ))) 0 := by
  let w := wt (ρ : ℤ) (-(s : ℤ))
  have hx : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w ρ := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 0)
  have hy : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w (-(s : ℤ)) := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 1)
  have hW : (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ :
      MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous w 0 := by
    convert (hx.pow s).mul (hy.pow ρ) using 1
    simp
    ring
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial n c =>
      rw [Polynomial.eval₂_monomial]
      simpa [w] using (hW.pow n).C_mul c

theorem crossingFace_general_weight
    (P : A1 ℂ) (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X])
    (hsρ : s < ρ) (hab : b < a)
    (hcut : cutPoly ρ (-(s : ℤ)) P.1 ≠ 0)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    vDeg ρ (-(s : ℤ)) P.1 =
      (k : ℤ)*(((ρ*a-s*b : ℕ) : ℤ)) := by
  have hW : s*b ≤ ρ*a := by
    have hsa : s*a ≤ ρ*a := Nat.mul_le_mul_right a hsρ.le
    have hsb : s*b ≤ s*a := Nat.mul_le_mul_left s hab.le
    omega
  let w := wt (ρ : ℤ) (-(s : ℤ))
  have hx : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w ρ := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 0)
  have hy : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w (-(s : ℤ)) := by
    simpa [w, wt] using (MvPolynomial.isWeightedHomogeneous_X ℂ w 1)
  have hR := crossing_general_scalar_substitution_homogeneous r ρ s
  have hbase : (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
      r.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) :
        MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      w (((ρ*a-s*b : ℕ) : ℤ)) := by
    convert ((hx.pow a).mul (hy.pow b)).mul hR using 1
    simp only [Nat.cast_sub hW, Nat.cast_mul, nsmul_eq_mul]
    ring
  have hfacehom : (leadingForm ρ (-(s : ℤ)) P.1).IsWeightedHomogeneous
      w ((k : ℤ)*(((ρ*a-s*b : ℕ) : ℤ))) := by
    rw [hface]
    convert (hbase.pow k).C_mul μ using 1 <;> ring
  have hfaceNonzero : leadingForm ρ (-(s : ℤ)) P.1 ≠ 0 := by
    intro hz
    apply hcut
    simp [cutPoly, hz]
  have hlead : (leadingForm ρ (-(s : ℤ)) P.1).IsWeightedHomogeneous
      w (vDeg ρ (-(s : ℤ)) P.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := w) (n := vDeg ρ (-(s : ℤ)) P.1)
  exact MvPolynomial.IsWeightedHomogeneous.inj_right hfaceNonzero hlead hfacehom

end Dixmier.Weyl
