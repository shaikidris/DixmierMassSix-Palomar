/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3Residual

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier

theorem appendix_A3_real_root_pos {h v : ℝ} (hh : 1 < h)
    (hphi : 48*h^2*v^2-24*h*(h+1)*v+3*h^2+4*h+1=0) : 0 < v := by
  by_contra hn
  have hv : v ≤ 0 := le_of_not_gt hn
  have hsq : 0 ≤ 48*h^2*v^2 := by positivity
  have hlin : 0 ≤ -24*h*(h+1)*v := by
    have : 0 ≤ -v := by linarith
    nlinarith [mul_nonneg (show 0 ≤ 24*h*(h+1) by positivity) this]
  have hc : 0 < 3*h^2+4*h+1 := by positivity
  nlinarith

end Dixmier

namespace Dixmier

theorem appendix_A3_real_part_root_pos {h : ℝ} {v : ℂ}
    (hh : 1 < h) (him : v.im=0)
    (hphi : appendix_A3_phi (h : ℂ) v=0) : 0 < v.re := by
  have hv : v = (v.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [hv] at hphi
  have hreal : 48*h^2*v.re^2-24*h*(h+1)*v.re+3*h^2+4*h+1=0 := by
    dsimp [appendix_A3_phi] at hphi
    exact_mod_cast hphi
  exact appendix_A3_real_root_pos hh hreal

end Dixmier
