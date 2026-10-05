/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3QuadraticBarrier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier

/-- Positivity of the third normalized companion coefficient at every real root
of the Appendix A.3 residual, for `h>1`. -/
theorem appendix_A3_b3_real_formula_pos {h v : ℝ} (hh : 1 < h)
    (hroot : 48*h^2*v^2-24*h*(h+1)*v+3*h^2+4*h+1=0) :
    0 < ((h+1)*(4*h*(9*h-5)*v-(h-1)*(3*h+1)))/
      (8*(h-1)*(2*h-1)*(3*h-1)) := by
  have ht := appendix_A3_tau_root_lt hh hroot
  have h9 : 0 < 9*h-5 := by linarith
  have hd : 0 < 4*h*(9*h-5) := by positivity
  have ht' := (div_lt_iff₀ hd).mp ht
  have hnum : 0 < 4*h*(9*h-5)*v-(h-1)*(3*h+1) := by nlinarith [ht']
  have hh1 : 0 < h-1 := by linarith
  have hh2 : 0 < 2*h-1 := by linarith
  have hh3 : 0 < 3*h-1 := by linarith
  positivity

end Dixmier
