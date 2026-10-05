/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FaceCutMass
public import Mathlib.Algebra.Polynomial.Expand

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Term count of a strict crossing face

For a face of the form `μ (x^a y^b r(x^s y^ρ))^k`, cutting at `x=1`
shifts and expands the exponents of `r^k` without changing its number of
nonzero terms. This supplies the `t(r^k) ≤ m(P)` step of Lemma 5.1.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

/-- Positive exponent expansion sends support exponents `n` to `n*ρ`. -/
theorem support_expand_eq (r : ℂ[X]) (ρ : ℕ) (hρ : 0 < ρ) :
    (Polynomial.expand ℂ ρ r).support = r.support.image (fun n => n * ρ) := by
  ext n
  constructor
  · intro hn
    have hc : (Polynomial.expand ℂ ρ r).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    rw [Polynomial.coeff_expand hρ] at hc
    split_ifs at hc with hdiv
    · refine Finset.mem_image.mpr ⟨n / ρ, Polynomial.mem_support_iff.mpr hc, ?_⟩
      exact Nat.div_mul_cancel hdiv
    · exact False.elim (hc rfl)
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    apply Polynomial.mem_support_iff.mpr
    simpa [Polynomial.coeff_expand_mul hρ] using (Polynomial.mem_support_iff.mp hm)

theorem termCount_expand_eq (r : ℂ[X]) (ρ : ℕ) (hρ : 0 < ρ) :
    termCount (Polynomial.expand ℂ ρ r) = termCount r := by
  rw [termCount, support_expand_eq r ρ hρ, termCount]
  exact Finset.card_image_of_injOn (by
    intro i _ j _ hij
    exact Nat.mul_right_cancel hρ hij)

/-- Multiplication by `X^b` shifts support exponents by `b`. -/
theorem support_X_pow_mul_eq (r : ℂ[X]) (b : ℕ) :
    (Polynomial.X ^ b * r).support = r.support.image (fun n => n + b) := by
  ext n
  constructor
  · intro hn
    have hc : (Polynomial.X ^ b * r).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    rw [Polynomial.coeff_X_pow_mul'] at hc
    split_ifs at hc with hbn
    · refine Finset.mem_image.mpr ⟨n - b, Polynomial.mem_support_iff.mpr hc, ?_⟩
      omega
    · exact False.elim (hc rfl)
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    apply Polynomial.mem_support_iff.mpr
    simpa [Polynomial.coeff_X_pow_mul] using (Polynomial.mem_support_iff.mp hm)

theorem termCount_X_pow_mul_eq (r : ℂ[X]) (b : ℕ) :
    termCount (Polynomial.X ^ b * r) = termCount r := by
  rw [termCount, support_X_pow_mul_eq r b, termCount]
  exact Finset.card_image_of_injOn (by
    intro i _ j _ hij
    exact Nat.add_right_cancel hij)

theorem support_C_mul_eq (r : ℂ[X]) (μ : ℂ) (hμ : μ ≠ 0) :
    (Polynomial.C μ * r).support = r.support := by
  ext n
  simp [Polynomial.mem_support_iff, Polynomial.coeff_C_mul, hμ]

theorem termCount_C_mul_eq (r : ℂ[X]) (μ : ℂ) (hμ : μ ≠ 0) :
    termCount (Polynomial.C μ * r) = termCount r := by
  simp [termCount, support_C_mul_eq r μ hμ]

/-- Under `x=1`, substitution `w=x^s y^ρ` becomes `w=y^ρ`. -/
theorem crossing_substitution_eval (r : ℂ[X]) (s ρ : ℕ) :
    MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)
      (r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) =
    r.comp (Polynomial.X ^ ρ) := by
  let g : Fin 2 → ℂ[X] := fun i => if i = 0 then 1 else Polynomial.X
  let φ := MvPolynomial.eval₂Hom Polynomial.C g
  have h := Polynomial.hom_eval₂ r MvPolynomial.C φ
    (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)
  have hcomp : φ.comp MvPolynomial.C = Polynomial.C := by
    ext c
    simp [φ]
  simp [φ, g] at h
  rw [show (MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)).comp MvPolynomial.C =
      Polynomial.C from hcomp] at h
  simpa [Polynomial.comp, Polynomial.eval₂_eq_eval_map] using h

/-- The precise cut polynomial of a general crossing face. -/
theorem crossingFace_general_cutPoly
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    cutPoly ρ (-(s : ℤ)) T.1 =
      Polynomial.C μ * Polynomial.X ^ (b * k) * Polynomial.expand ℂ ρ (r ^ k) := by
  rw [cutPoly, hface]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_pow]
  rw [crossing_substitution_eval]
  rw [← Polynomial.expand_eq_comp_X_pow]
  simp [mul_pow, ← map_pow, pow_mul, mul_assoc]

/-- The selected face's actual cut polynomial has the endpoint order
predicted by its powered scalar factor. -/
theorem crossingFace_general_cutPoly_natDegree
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ)
    (hμ : μ ≠ 0) (hρ : 0 < ρ) (hr0 : r.coeff 0 = 1)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    (cutPoly ρ (-(s : ℤ)) T.1).natDegree =
      b*k + ρ*k*r.natDegree := by
  have hr : r ≠ 0 := by
    intro hz
    simp [hz] at hr0
  rw [crossingFace_general_cutPoly μ a b s ρ k r T hface]
  rw [mul_assoc]
  rw [Polynomial.natDegree_C_mul hμ,
    Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      ((Polynomial.expand_ne_zero hρ).mpr (pow_ne_zero _ hr)),
    Polynomial.natDegree_X_pow, Polynomial.natDegree_expand,
    Polynomial.natDegree_pow]
  ring

/-- The zero root of the actual cut polynomial comes only from the
displayed `y^b` base: the normalized scalar factor has constant term
one, even after expansion and outer powering. -/
theorem crossingFace_general_cutPoly_zero_rootMultiplicity
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ)
    (hμ : μ ≠ 0) (hρ : 0 < ρ) (hr0 : r.coeff 0 = 1)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    (cutPoly ρ (-(s : ℤ)) T.1).rootMultiplicity 0 = b*k := by
  let g : ℂ[X] := Polynomial.C μ * Polynomial.expand ℂ ρ (r ^ k)
  have heval : r.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hr0
  have hconst : (Polynomial.expand ℂ ρ (r ^ k)).coeff 0 = 1 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, heval] using
      (Polynomial.coeff_expand_mul' hρ (r ^ k) 0)
  have hg0 : g.eval 0 ≠ 0 := by
    change (Polynomial.C μ * Polynomial.expand ℂ ρ (r ^ k)).eval 0 ≠ 0
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have he : (Polynomial.expand ℂ ρ (r ^ k)).eval 0 = 1 := by
      simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hconst
    simpa only [he, mul_one] using hμ
  have hg : g ≠ 0 := by
    intro hz
    exact hg0 (by simp [hz])
  have hzero : g.rootMultiplicity 0 = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hg0)
  rw [crossingFace_general_cutPoly μ a b s ρ k r T hface]
  have hshape : Polynomial.C μ * Polynomial.X ^ (b*k) *
      Polynomial.expand ℂ ρ (r^k) = g * Polynomial.X ^ (b*k) := by
    dsimp [g]
    ring
  rw [hshape]
  simpa only [map_zero, sub_zero, hzero, zero_add] using
    (Polynomial.rootMultiplicity_mul_X_sub_C_pow (a := (0 : ℂ))
      (n := b*k) hg)

/-- A nonzero scalar, monomial shift and positive exponent expansion preserve `t(r^k)`. -/
theorem crossingFace_general_termCount_eq
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ)
    (hμ : μ ≠ 0) (hρ : 0 < ρ)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    termCount (cutPoly ρ (-(s : ℤ)) T.1) = termCount (r ^ k) := by
  rw [crossingFace_general_cutPoly μ a b s ρ k r T hface]
  rw [mul_assoc, termCount_C_mul_eq _ μ hμ,
    termCount_X_pow_mul_eq, termCount_expand_eq _ ρ hρ]

/-- The paper's `t(r^k) ≤ m(P)` inequality for any explicitly represented crossing face. -/
theorem crossingFace_general_termCount_le_mass
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ)
    (hμ : μ ≠ 0) (hsρ : s < ρ)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    termCount (r ^ k) ≤ mass T.1 := by
  rw [← crossingFace_general_termCount_eq μ a b s ρ k r T hμ (by omega) hface]
  exact cutPoly_termCount_le_mass T ρ (-(s : ℤ)) (by omega)

end Dixmier.Weyl
