/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CompanionLattice

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Reconstructing the strict-crossing companion

The lattice theorem places every coefficient of a weight-`ρ-s` companion
on the ray `(1+st,1+ρt)`. A finite sum of those coefficients gives an
ordinary polynomial `f` and the exact identity `F=xy f(x^s y^ρ)`.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

private theorem monomial_expo (i j : ℕ) (c : ℂ) :
    MvPolynomial.monomial (expo i j) c =
      MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j := by
  simp [expo, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.C_mul_monomial]

private theorem companion_monomial (s ρ t : ℕ) (c : ℂ) :
    MvPolynomial.monomial (expo (1 + s * t) (1 + ρ * t)) c =
      MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) *
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ t := by
  rw [monomial_expo]
  simp [mul_pow, pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Every primitive weight-`ρ-s` companion has the exact polynomial form
`xy f(x^s y^ρ)`. The constructed `f` has finite support; no degree bound
is imposed. -/
theorem companion_homogeneous_shape
    (F : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hF : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s)) :
    ∃ f : ℂ[X], F = MvPolynomial.X 0 * MvPolynomial.X 1 *
      f.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) := by
  classical
  have hsupport := companion_support_lattice F ρ s hs hsρ hc hF
  let τ (d : Fin 2 →₀ ℕ) : ℕ :=
    if hd : d ∈ F.support then Classical.choose (hsupport d hd) else 0
  have hτ (d : Fin 2 →₀ ℕ) (hd : d ∈ F.support) :
      d = expo (1 + s * τ d) (1 + ρ * τ d) := by
    simp only [τ, dif_pos hd]
    exact Classical.choose_spec (hsupport d hd)
  let f : ℂ[X] := ∑ d ∈ F.support, Polynomial.C (MvPolynomial.coeff d F) *
    Polynomial.X ^ τ d
  let W : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ
  refine ⟨f, ?_⟩
  have heval : f.eval₂ MvPolynomial.C W =
      ∑ d ∈ F.support, MvPolynomial.C (MvPolynomial.coeff d F) *
        W ^ τ d := by
    dsimp [f]
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  calc
    F = ∑ d ∈ F.support, MvPolynomial.monomial d (MvPolynomial.coeff d F) := F.as_sum
    _ = (MvPolynomial.X 0 * MvPolynomial.X 1) *
        (∑ d ∈ F.support, MvPolynomial.C (MvPolynomial.coeff d F) *
          W ^ τ d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      calc
        MvPolynomial.monomial d (MvPolynomial.coeff d F) =
            MvPolynomial.monomial (expo (1 + s * τ d) (1 + ρ * τ d))
              (MvPolynomial.coeff d F) :=
                congrArg (fun e => MvPolynomial.monomial e (MvPolynomial.coeff d F))
                  (hτ d hd)
        _ = MvPolynomial.C (MvPolynomial.coeff d F) *
              (MvPolynomial.X 0 * MvPolynomial.X 1) * W ^ τ d := by
                simpa only [W] using
                  (companion_monomial s ρ (τ d) (MvPolynomial.coeff d F))
        _ = (MvPolynomial.X 0 * MvPolynomial.X 1) *
              (MvPolynomial.C (MvPolynomial.coeff d F) * W ^ τ d) := by ring
    _ = (MvPolynomial.X 0 * MvPolynomial.X 1) *
        f.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) := by
      change (MvPolynomial.X 0 * MvPolynomial.X 1) *
        (∑ d ∈ F.support, MvPolynomial.C (MvPolynomial.coeff d F) * W ^ τ d) =
        (MvPolynomial.X 0 * MvPolynomial.X 1) * f.eval₂ MvPolynomial.C W
      exact congrArg (fun z : MvPolynomial (Fin 2) ℂ =>
        (MvPolynomial.X 0 * MvPolynomial.X 1) * z) heval.symm

end Dixmier.Weyl
