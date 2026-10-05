/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedLaurent
public import Mathlib.RingTheory.Derivation.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The ramified coefficient derivation

The scaled Laurent derivative is packaged as a derivation so it can be
used as the coefficient derivation of a finite-order differential-operator
algebra. The latter algebra and the G13 cut remain separate obligations.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedDerivation (l : ℕ) :
    Derivation ℂ (LaurentPolynomial ℂ) (LaurentPolynomial ℂ) :=
  Derivation.mk' (ramifiedDerivative l) (by
    intro f g
    simpa only [smul_eq_mul, mul_comm, add_comm] using
      ramifiedDerivative_mul l f g)

/-- Multiplication by an arbitrary ramified Laurent coefficient. -/
noncomputable def ramifiedCoeffMul (f : LaurentPolynomial ℂ) :
    Module.End ℂ (LaurentPolynomial ℂ) :=
  LinearMap.mulLeft ℂ f

/-- Exact normal-ordering rule: `Y f - f Y = (d/dX) f`. -/
theorem ramifiedDerivative_coeff_comm (l : ℕ) (f : LaurentPolynomial ℂ) :
    ramifiedDerivative l * ramifiedCoeffMul f -
      ramifiedCoeffMul f * ramifiedDerivative l =
      ramifiedCoeffMul (ramifiedDerivative l f) := by
  apply LinearMap.ext
  intro g
  change ramifiedDerivative l (f * g) -
    f * ramifiedDerivative l g = ramifiedDerivative l f * g
  rw [ramifiedDerivative_mul]
  abel

end Dixmier.Weyl
