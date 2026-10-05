module

public import DixmierFormal.Weyl.WronskianRatio
public import Mathlib.LinearAlgebra.Dimension.Finite
public import DixmierFormal.Weyl.RamifiedTopFacePolynomial

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Scalar rigidity in a ramified homogeneous face centralizer

Canonical ramified top faces are ordinary polynomials in derivative order.
At a fixed weight their vanishing first-contraction bracket is a common
first-order differential equation. Its solution space has at most one
scalar direction. No restriction on Laurent exponents is needed here.
-/

namespace Dixmier.Weyl
open Polynomial

theorem weighted_derivative_kernel_scalar_ratio
    (f g h : ℂ[X]) (a b : ℂ) (ha : a ≠ 0) (hf : f ≠ 0) (hh : h ≠ 0)
    (hg : C a * f * g.derivative - C b * f.derivative * g = 0)
    (hhEq : C a * f * h.derivative - C b * f.derivative * h = 0) :
    ∃ c : ℂ, g = C c * h := by
  have hcancel : C a * f * (h * g.derivative - g * h.derivative) = 0 := by
    linear_combination h * hg - g * hhEq
  have haC : (C a : ℂ[X]) ≠ 0 := by simpa using ha
  have hw : h * g.derivative - g * h.derivative = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left (mul_ne_zero haC hf)
  apply polynomial_wronskian_zero_scalar_ratio g h hh
  simp only [Polynomial.wronskian]
  linear_combination -hw

theorem weighted_derivative_kernel_finrank_le_one
    (S : Submodule ℂ ℂ[X]) (f : ℂ[X]) (a b : ℂ)
    (ha : a ≠ 0) (hf : f ≠ 0)
    (hS : ∀ g : S, C a * f * g.val.derivative - C b * f.derivative * g.val = 0) :
    Module.finrank ℂ S ≤ 1 := by
  classical
  by_cases hex : ∃ h : S, h ≠ 0
  · obtain ⟨h, hh⟩ := hex
    apply finrank_le_one h
    intro g
    have hhval : h.val ≠ 0 := by
      intro hz
      exact hh (Subtype.ext hz)
    obtain ⟨c, hc⟩ := weighted_derivative_kernel_scalar_ratio
      f g.val h.val a b ha hf hhval (hS g) (hS h)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change c • h.val = g.val
    simpa only [Algebra.smul_def, Polynomial.algebraMap_eq] using hc.symm
  · apply finrank_le_one (0 : S)
    intro g
    have hg : g = 0 := by
      by_contra hn
      exact hex ⟨g, hn⟩
    exact ⟨0, by simp [hg]⟩

/-- Apply the kernel bound to an actual canonical ramified top face.
The scalar coefficients are precisely those in the first-contraction
commutator formula. The candidate centralizer weight may have either sign. -/
theorem ramified_top_face_centralizer_finrank_le_one
    (l : ℕ) (hl : 0 < l) (ρ σ n : ℤ) (hρ : 0 < ρ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0)
    (hweight : ramifiedWeightDeg l hl ρ σ P ≠ 0)
    (S : Submodule ℂ ℂ[X])
    (hS : ∀ g : S,
      C ((ramifiedWeightDeg l hl ρ σ P : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
        ramifiedTopFacePolynomial l hl ρ σ P * g.val.derivative -
      C ((n : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative * g.val = 0) :
    Module.finrank ℂ S ≤ 1 := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hmC : (ramifiedWeightDeg l hl ρ σ P : ℂ) ≠ 0 := by
    exact_mod_cast hweight
  exact weighted_derivative_kernel_finrank_le_one S
    (ramifiedTopFacePolynomial l hl ρ σ P) _ _
    (div_ne_zero hmC (mul_ne_zero hlC hρC))
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP) hS

end Dixmier.Weyl
