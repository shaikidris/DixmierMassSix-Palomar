/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3PositiveReal

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier

private theorem im_zero_of_sq_eq_positive_real {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hsq : z^2=(r : ℂ)) : z.im=0 := by
  have him := congrArg Complex.im hsq
  have hre := congrArg Complex.re hsq
  simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re] at him hre
  by_cases hz : z.im=0
  · exact hz
  have hzre : z.re=0 := by
    have hm : z.re*z.im=0 := by nlinarith [him]
    exact (mul_eq_zero.mp hm).resolve_right hz
  rw [hzre] at hre
  nlinarith [sq_nonneg z.im]

/-- Every complex root of the Appendix A.3 residual is real when `h > 1`. -/
theorem appendix_A3_complex_root_real {h : ℝ} {v : ℂ}
    (hh : 1 < h) (hphi : appendix_A3_phi (h : ℂ) v=0) : v.im=0 := by
  have hh0 : h ≠ 0 := by linarith
  have hh0c : (h : ℂ) ≠ 0 := by exact_mod_cast hh0
  let c : ℝ := (h+1)/(4*h)
  let r : ℝ := (h+1)/(24*h^2)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hsq : (v-(c:ℂ))^2=(r:ℂ) := by
    dsimp [c,r]
    dsimp [appendix_A3_phi] at hphi
    push_cast
    field_simp [hh0c] at hphi ⊢
    linear_combination 8*hphi
  have hi := im_zero_of_sq_eq_positive_real hr hsq
  have hcim : (c:ℂ).im=0 := by simp
  have := congrArg Complex.im (show v=(v-(c:ℂ))+(c:ℂ) by ring)
  simp only [Complex.add_im, Complex.sub_im, hcim, sub_zero, add_zero] at this
  simpa [this] using hi

/-- The residual root is a positive real number, expressed through its complex coordinates. -/
theorem appendix_A3_complex_root_re_pos {h : ℝ} {v : ℂ}
    (hh : 1 < h) (hphi : appendix_A3_phi (h : ℂ) v=0) : 0 < v.re := by
  exact appendix_A3_real_part_root_pos hh (appendix_A3_complex_root_real hh hphi) hphi

end Dixmier
