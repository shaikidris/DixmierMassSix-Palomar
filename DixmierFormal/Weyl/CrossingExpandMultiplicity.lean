/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingTermCount
public import DixmierFormal.Scalar.Section6Roots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root multiplicity under characteristic-zero power substitution

At a nonzero complex point, `X ↦ X^ρ` is unramified. The Frobenius
`rootMultiplicity_expand` theorem does not cover this characteristic-zero
case, so we prove the needed equality from the root factorization.
-/

namespace Dixmier.Weyl
open Polynomial

theorem X_pow_sub_C_rootMultiplicity_one_at_nonzero
    (ρ : ℕ) (c : ℂ) (hρ : 0 < ρ) (hc : c ≠ 0) :
    (X ^ ρ - C (c ^ ρ) : ℂ[X]).rootMultiplicity c = 1 := by
  have hp : (X ^ ρ - C (c ^ ρ) : ℂ[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero hρ (c ^ ρ)
  have hroot : (X ^ ρ - C (c ^ ρ) : ℂ[X]).IsRoot c := by
    simp [Polynomial.IsRoot]
  have hpos : 0 < (X ^ ρ - C (c ^ ρ) : ℂ[X]).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hp).mpr hroot
  have hder : (derivative (X ^ ρ - C (c ^ ρ) : ℂ[X])).eval c ≠ 0 := by
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_C, eval_pow, eval_X]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hρ)
      (pow_ne_zero _ hc)
  have hlt : ¬ 1 < (X ^ ρ - C (c ^ ρ) : ℂ[X]).rootMultiplicity c := by
    intro h
    have hd := ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mp h).2
    exact hder hd
  omega

theorem rootMultiplicity_expand_at_nonzero
    (ρ : ℕ) (r : ℂ[X]) (c : ℂ) (hρ : 0 < ρ) (hc : c ≠ 0)
    (hr : r ≠ 0) :
    (Polynomial.expand ℂ ρ r).rootMultiplicity c =
      r.rootMultiplicity (c ^ ρ) := by
  obtain ⟨u, hru, hndvd⟩ :=
    r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr (c ^ ρ)
  have hueval : u.eval (c ^ ρ) ≠ 0 := by
    intro hz
    exact hndvd (Polynomial.dvd_iff_isRoot.mpr hz)
  have huexp : (Polynomial.expand ℂ ρ u).eval c ≠ 0 := by
    rw [Polynomial.expand_eval]
    exact hueval
  have hune : Polynomial.expand ℂ ρ u ≠ 0 := by
    intro hz
    exact huexp (by simp [hz])
  have hfactor : Polynomial.expand ℂ ρ r =
      (X ^ ρ - C (c ^ ρ)) ^ (r.rootMultiplicity (c ^ ρ)) *
        Polynomial.expand ℂ ρ u := by
    conv_lhs => rw [hru]
    rw [map_mul, map_pow, map_sub, Polynomial.expand_X, Polynomial.expand_C]
  rw [hfactor]
  have hfirst : (X ^ ρ - C (c ^ ρ) : ℂ[X]) ^
      (r.rootMultiplicity (c ^ ρ)) ≠ 0 :=
    pow_ne_zero _ (X_pow_sub_C_ne_zero hρ (c ^ ρ))
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfirst hune),
    Dixmier.section6_rootMultiplicity_pow,
    X_pow_sub_C_rootMultiplicity_one_at_nonzero ρ c hρ hc]
  have hu0 : (Polynomial.expand ℂ ρ u).rootMultiplicity c = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using huexp)
  simp [hu0]

/-- At a nonzero cut root, the base monomial and scalar contribute no
multiplicity; the outer power contributes exactly its exponent. -/
theorem crossingFace_general_cutPoly_nonzero_rootMultiplicity
    (μ : ℂ) (a b s ρ k : ℕ) (r : ℂ[X]) (T : A1 ℂ) (c : ℂ)
    (hμ : μ ≠ 0) (hρ : 0 < ρ) (hr0 : r.coeff 0 = 1) (hc : c ≠ 0)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    (cutPoly ρ (-(s : ℤ)) T.1).rootMultiplicity c =
      k * r.rootMultiplicity (c ^ ρ) := by
  have hr : r ≠ 0 := by
    intro hz
    simp [hz] at hr0
  let g : ℂ[X] := C μ * X ^ (b*k)
  have hg0 : g.eval c ≠ 0 := by
    change (C μ * X ^ (b*k) : ℂ[X]).eval c ≠ 0
    simpa only [eval_mul, eval_C, eval_pow, eval_X] using
      mul_ne_zero hμ (pow_ne_zero (b*k) hc)
  have hg : g ≠ 0 := by
    intro hz
    exact hg0 (by simp [hz])
  have he : Polynomial.expand ℂ ρ r ≠ 0 :=
    (Polynomial.expand_ne_zero hρ).mpr hr
  have hpow : (Polynomial.expand ℂ ρ r) ^ k ≠ 0 := pow_ne_zero _ he
  rw [crossingFace_general_cutPoly μ a b s ρ k r T hface]
  have hshape : C μ * X ^ (b*k) * Polynomial.expand ℂ ρ (r^k) =
      g * (Polynomial.expand ℂ ρ r) ^ k := by
    simp only [g, map_pow]
  rw [hshape, Polynomial.rootMultiplicity_mul (mul_ne_zero hg hpow),
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hg0),
    Dixmier.section6_rootMultiplicity_pow,
    rootMultiplicity_expand_at_nonzero ρ r c hρ hc hr]
  omega

end Dixmier.Weyl
