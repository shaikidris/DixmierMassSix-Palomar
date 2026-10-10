theory Homogeneous_Centralizer_Line
  imports Homogeneous_Power_Ratio
begin

lemma homogeneous_poisson_centralizer_scalar_ratio:
  fixes f g h :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hh: "weighted_homogeneous rho sigma n h"
    and hfne: "f\<noteq>0" and hm: "m\<noteq>0" and hhne: "h\<noteq>0"
    and hfg: "biv_poisson f g=0" and hfh: "biv_poisson f h=0"
  shows "\<exists>c::complex. g=[:[:c:]:]*h"
proof -
  have hgf: "biv_poisson g f=0" using hfg by (simp add: biv_poisson_def algebra_simps)
  have hhf: "biv_poisson h f=0" using hfh by (simp add: biv_poisson_def algebra_simps)
  note hdg = homogeneous_poisson_derivative_identities[OF hg hf hgf]
  note hdh = homogeneous_poisson_derivative_identities[OF hh hf hhf]
  have nonzero: "([:[:of_int m:]:]*f::complex bivariate)\<noteq>0"
    using hm hfne by simp
  have cross_x_zero: "([:[:of_int m:]:]*f)*(h*biv_dx g-g*biv_dx h)=0"
    using hdg hdh by algebra
  have cross_y_zero: "([:[:of_int m:]:]*f)*(h*biv_dy g-g*biv_dy h)=0"
    using hdg hdh by algebra
  have cross_x: "h*biv_dx g=g*biv_dx h" using cross_x_zero nonzero by simp
  have cross_y: "h*biv_dy g=g*biv_dy h" using cross_y_zero nonzero by simp
  show ?thesis by (rule bivariate_cross_derivatives_constant[OF hhne cross_x cross_y])
qed

end
