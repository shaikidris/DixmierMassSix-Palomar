/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3FirstSigns

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier

/-- A root of an upward-opening quadratic lies to the right of any positive-valued
test point strictly left of the vertex. The Appendix A.3 test point is `τ`. -/
theorem quadratic_root_gt_test {a b c t v : ℝ}
    (ha : 0 < a) (hleft : b + 2*a*t < 0)
    (htest : 0 < a*t^2+b*t+c)
    (hroot : a*v^2+b*v+c=0) : t < v := by
  by_contra hn
  have hvt : v ≤ t := le_of_not_gt hn
  have hfactor : a*(v+t)+b < 0 := by nlinarith
  have hprod : 0 ≤ (t-v)*(-(a*(v+t)+b)) := by
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod]

/-- For the Appendix A.3 residual, every real root lies above the manuscript's
test point `τ = (h-1)(3h+1)/(4h(9h-5))`. -/
theorem appendix_A3_tau_root_lt {h v : ℝ} (hh : 1 < h)
    (hroot : 48*h^2*v^2-24*h*(h+1)*v+3*h^2+4*h+1=0) :
    (h-1)*(3*h+1)/(4*h*(9*h-5)) < v := by
  let t := (h-1)*(3*h+1)/(4*h*(9*h-5))
  have h9 : 0 < 9*h-5 := by linarith
  have h0 : 0 < h := by linarith
  have hd : 4*h*(9*h-5) ≠ 0 := ne_of_gt (by positivity)
  have ht : (4*h*(9*h-5))*t=(h-1)*(3*h+1) := by
    dsimp [t]
    simpa [mul_comm] using (div_mul_cancel₀ ((h-1)*(3*h+1)) hd)
  have hleft : -24*h*(h+1)+2*(48*h^2)*t < 0 := by
    have hid : -24*h*(h+1)+2*(48*h^2)*t =
        -48*h*(3*h^2+3*h-2)/(9*h-5) := by
      apply (eq_div_iff (ne_of_gt h9)).2
      linear_combination 24*h*ht
    rw [hid]
    have hn : 0 < 3*h^2+3*h-2 := by nlinarith
    have hp : 0 < 48*h*(3*h^2+3*h-2) := by positivity
    exact div_neg_of_neg_of_pos (by nlinarith) h9
  have htest : 0 < 48*h^2*t^2-24*h*(h+1)*t+3*h^2+4*h+1 := by
    have hid : 48*h^2*t^2-24*h*(h+1)*t+3*h^2+4*h+1 =
        2*(2*h-1)*(3*h+1)^3/(9*h-5)^2 := by
      apply (eq_div_iff (pow_ne_zero 2 (ne_of_gt h9))).2
      linear_combination 3*(36*h^2*t-15*h^2-20*h*t-10*h+9)*ht
    rw [hid]
    have h2 : 0 < 2*h-1 := by linarith
    positivity
  have hroot' : (48*h^2)*v^2 + (-24*h*(h+1))*v + (3*h^2+4*h+1) = 0 := by
    convert hroot using 1 <;> ring
  have htest' : 0 < (48*h^2)*t^2 + (-24*h*(h+1))*t + (3*h^2+4*h+1) := by
    convert htest using 1 <;> ring
  exact quadratic_root_gt_test (show 0 < 48*h^2 by positivity) hleft htest' hroot'

end Dixmier
