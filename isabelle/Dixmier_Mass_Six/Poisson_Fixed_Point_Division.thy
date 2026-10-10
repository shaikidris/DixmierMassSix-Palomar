theory Poisson_Fixed_Point_Division
  imports "Poisson_Power_Cancellation"
begin

lemma poisson_mul_right:
  fixes f g h :: "complex bivariate"
  shows "biv_poisson f (g*h) = biv_poisson f g * h + g * biv_poisson f h"
  by (simp only: biv_poisson_def biv_dx_mult biv_dy_mult)
    (simp add: algebra_simps)

lemma poisson_self:
  fixes f :: "complex bivariate"
  shows "biv_poisson f f = 0"
  by (simp add: biv_poisson_def mult.commute)

lemma poisson_fixed_point_of_division:
  fixes f g h F :: "complex bivariate"
  assumes "h\<noteq>0" "biv_poisson f g = h"
    "biv_poisson f h = 0" "h*F=f*g"
  shows "biv_poisson f F = f"
proof -
  have left: "biv_poisson f (h*F)=h*biv_poisson f F"
    by (simp only: poisson_mul_right assms(3)) simp
  have right: "biv_poisson f (f*g)=f*h"
    by (simp only: poisson_mul_right poisson_self assms(2)) simp
  have equal: "h*biv_poisson f F=h*f"
    using left right assms(4) by (metis mult.commute)
  show ?thesis using equal assms(1) by simp
qed

end
