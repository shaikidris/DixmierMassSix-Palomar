/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3ComplexRoot

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier

/-- Positivity of the first normalized companion coefficient in Proposition A.3. -/
theorem appendix_A3_b1_real_formula_pos {h : ℝ} (hh : 1 < h) :
    0 < (3*h+1)/(2*(h-1)) := by
  have hh1 : 0 < h-1 := by linarith
  positivity

/-- Positivity of the second normalized companion coefficient in Proposition A.3. -/
theorem appendix_A3_b2_real_formula_pos {h v : ℝ} (hh : 1 < h) (hv : 0 < v) :
    0 < (12*h*(h-1)*v+3*h^2+4*h+1)/(4*(h-1)*(2*h-1)) := by
  have hh1 : 0 < h-1 := by linarith
  have hh2 : 0 < 2*h-1 := by linarith
  positivity

end Dixmier
