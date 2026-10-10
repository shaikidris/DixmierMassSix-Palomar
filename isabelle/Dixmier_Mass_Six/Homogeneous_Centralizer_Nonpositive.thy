theory Homogeneous_Centralizer_Nonpositive
  imports Poisson_Positive_Bracket_Polynomiality
begin

lemma positive_weight_homogeneous_not_isUnit:
  fixes f :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f" and hm: "0<m"
  shows "\<not>is_unit f"
proof
  assume "is_unit f"
  then obtain U where outer: "f=[:U:]" and unitU: "is_unit U"
    by (rule is_unit_polyE)
  obtain c where inner: "U=[:c:]" and cunit: "c dvd 1"
    using unitU by (rule is_unit_polyE)
  have cnz: "c\<noteq>0" using cunit by auto
  have mem: "(0,0)\<in>biv_support f"
    using outer inner cnz by (simp add: biv_support_def biv_coeff_def)
  have "m=0" using hf mem by (auto simp: weighted_homogeneous_def pair_weight_def)
  then show False using hm by arith
qed

lemma homogeneous_poisson_centralizer_weight_nonnegative:
  fixes f h :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hh: "weighted_homogeneous rho sigma n h"
    and hfne: "f\<noteq>0" and hhne: "h\<noteq>0" and hm: "0<m"
    and hbr: "biv_poisson h f=0"
  shows "0\<le>n"
proof (rule ccontr)
  assume "\<not>0\<le>n"
  then have hn: "n<0" by arith
  obtain a where na: "-n=int (Suc a)"
  proof -
    have "0<nat (-n)" using hn by simp
    then obtain a where "nat (-n)=Suc a" by (cases "nat (-n)") auto
    then show thesis using that[of a] hn by simp
  qed
  obtain b where mb: "m=int (Suc b)"
  proof -
    have "0<nat m" using hm by simp
    then obtain b where "nat m=Suc b" by (cases "nat m") auto
    then show thesis using that[of b] hm by simp
  qed
  note der = homogeneous_poisson_derivative_identities[OF hh hf hbr]
  have zero: "biv_deriv is_y (f^Suc a*h^Suc b)=0" for is_y
  proof -
    have hi: "[:[:of_int m:]:]*(f*biv_deriv is_y h)=[:[:of_int n:]:]*(h*biv_deriv is_y f)"
      using der by (cases is_y) (simp_all add: biv_deriv_def)
    have n_eq: "n=-int (Suc a)" using na by arith
    have ncast: "(of_int n::complex)=-of_nat (Suc a)" by (simp add: n_eq)
    have mcast: "(of_int m::complex)=of_nat (Suc b)" by (simp only: mb of_int_of_nat_eq)
    have scalar_n: "([:[:of_int n:]:]::complex bivariate)=-of_nat (Suc a)"
      by (simp add: ncast of_nat_poly)
    have scalar_m: "([:[:of_int m:]:]::complex bivariate)=of_nat (Suc b)"
      by (simp add: mcast of_nat_poly)
    have balance: "of_nat (Suc a)*h*biv_deriv is_y f + of_nat (Suc b)*f*biv_deriv is_y h=0"
      using hi by (simp only: scalar_n scalar_m) algebra
    have dmul: "biv_deriv is_y (F*G)=biv_deriv is_y F*G+F*biv_deriv is_y G" for F G
      by (cases is_y) (simp_all add: biv_deriv_def biv_dx_mult biv_dy_mult)
    have dpow: "biv_deriv is_y (F^Suc k)=of_nat (Suc k)*F^k*biv_deriv is_y F" for F k
      by (cases is_y) (simp_all only: biv_deriv_def if_True if_False biv_dx_power_Suc biv_dy_power_Suc)
    have factor: "biv_deriv is_y (f^Suc a*h^Suc b)=
        f^a*h^b*(of_nat (Suc a)*h*biv_deriv is_y f+of_nat (Suc b)*f*biv_deriv is_y h)"
      by (simp only: dmul dpow) (simp only: power_Suc; algebra)
    show ?thesis by (simp only: factor balance mult_zero_right)
  qed
  have dx: "1*biv_dx (f^Suc a*h^Suc b)=(f^Suc a*h^Suc b)*biv_dx 1"
    using zero[of False] by (simp add: biv_deriv_def)
  have dy: "1*biv_dy (f^Suc a*h^Suc b)=(f^Suc a*h^Suc b)*biv_dy 1"
    using zero[of True] by (simp add: biv_deriv_def)
  obtain c where scalar: "f^Suc a*h^Suc b=[:[:c:]:]*1"
    using bivariate_cross_derivatives_constant[OF one_neq_zero dx dy] by blast
  have cnz: "c\<noteq>0" using scalar hfne hhne by auto
  have "is_unit (f^Suc a*h^Suc b)"
    using scalar bivariate_scalar_unit[OF cnz] by simp
  then have "is_unit f" by (simp add: is_unit_mult_iff is_unit_power_iff)
  then show False using positive_weight_homogeneous_not_isUnit[OF hf hm] by contradiction
qed

lemma homogeneous_poisson_centralizer_weight_zero_constant:
  fixes f h :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hh: "weighted_homogeneous rho sigma 0 h"
    and hfne: "f\<noteq>0" and hm: "m\<noteq>0" and hbr: "biv_poisson f h=0"
  shows "\<exists>c::complex. h=[:[:c:]:]"
proof -
  note der = homogeneous_poisson_derivative_identities[OF hf hh hbr]
  have cnz: "([:[:of_int m:]:]::complex bivariate)\<noteq>0" using hm by simp
  have dx: "biv_dx h=0" and dy: "biv_dy h=0"
    using der cnz hfne by auto
  have cross_x: "1*biv_dx h=h*biv_dx 1" using dx by simp
  have cross_y: "1*biv_dy h=h*biv_dy 1" using dy by simp
  show ?thesis using bivariate_cross_derivatives_constant[OF one_neq_zero cross_x cross_y] by simp
qed

lemma poisson_homogeneous_fixed_point_of_constant_bracket:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hc: "c\<noteq>0" and hbr: "biv_poisson f g=[:[:c:]:]"
  shows "\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and> biv_poisson f F=f"
proof -
  let ?F = "[:[:inverse c:]:]*(f*g)"
  have div: "biv_poisson f g*?F=f*g"
    by (rule biv_eqI) (use hbr hc in \<open>simp add: mult.assoc[symmetric]\<close>)
  have br: "biv_poisson f g\<noteq>0" using hbr hc by simp
  have second: "biv_poisson f (biv_poisson f g)=0"
    by (simp only: hbr) (simp add: biv_poisson_def)
  have fixed: "biv_poisson f ?F=f \<and> weighted_homogeneous rho sigma (rho+sigma) ?F"
    by (rule poisson_fixed_point_of_two_brackets_and_division[OF hf hg br second div])
  show ?thesis using fixed by blast
qed

lemma poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hfne: "f\<noteq>0" and hm: "0<m"
    and hbr: "biv_poisson f g\<noteq>0"
    and hsecond: "biv_poisson f (biv_poisson f g)=0"
    and hweight: "m+n-(rho+sigma)\<le>0"
  shows "\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and> biv_poisson f F=f"
proof -
  have hh: "weighted_homogeneous rho sigma (m+n-(rho+sigma)) (biv_poisson f g)"
    by (rule poisson_weighted_homogeneous_signed[OF hf hg])
  have swap: "biv_poisson (biv_poisson f g) f=0"
    using hsecond by (simp add: biv_poisson_def algebra_simps)
  have nonnegative: "0\<le>m+n-(rho+sigma)"
    by (rule homogeneous_poisson_centralizer_weight_nonnegative[OF hf hh hfne hbr hm swap])
  have weight_zero: "m+n-(rho+sigma)=0" using hweight nonnegative by arith
  have hz: "weighted_homogeneous rho sigma 0 (biv_poisson f g)" using hh weight_zero by simp
  have mnz: "m\<noteq>0" using hm by arith
  obtain c where scalar_bracket: "biv_poisson f g=[:[:c:]:]"
    using homogeneous_poisson_centralizer_weight_zero_constant[OF hf hz hfne mnz hsecond] by blast
  have cnz: "c\<noteq>0" using hbr scalar_bracket by auto
  show ?thesis by (rule poisson_homogeneous_fixed_point_of_constant_bracket[OF hf hg cnz scalar_bracket])
qed

end
