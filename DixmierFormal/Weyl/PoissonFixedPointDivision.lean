/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CompanionPowerCancellation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A polynomial division criterion for a Poisson fixed point

This isolates the algebraic last step in Joseph's two-bracket route.
Producing a nonzero `h = {f,g}` that centralizes `f` and divides `f*g`
remains a separate, source-level existence theorem.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem poisson_mul_right (f g h : MvPolynomial (Fin 2) ℂ) :
    poisson f (g*h) = poisson f g * h + g * poisson f h := by
  simp only [poisson, MvPolynomial.pderiv_mul]
  ring

theorem poisson_self (f : MvPolynomial (Fin 2) ℂ) :
    poisson f f = 0 := by
  simp only [poisson]
  ring

theorem poisson_fixed_point_of_division
    (f g h F : MvPolynomial (Fin 2) ℂ)
    (hh : h ≠ 0)
    (hbr : poisson f g = h)
    (hcentral : poisson f h = 0)
    (hdiv : h * F = f * g) :
    poisson f F = f := by
  have hleft : poisson f (h*F) = h * poisson f F := by
    rw [poisson_mul_right, hcentral]
    ring
  have hright : poisson f (f*g) = f*h := by
    rw [poisson_mul_right, poisson_self, hbr]
    ring
  rw [hdiv] at hleft
  rw [hright] at hleft
  rw [mul_comm f h] at hleft
  exact mul_left_cancel₀ hh hleft.symm

end Dixmier.Weyl
