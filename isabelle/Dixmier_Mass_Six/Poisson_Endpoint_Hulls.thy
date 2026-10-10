theory Poisson_Endpoint_Hulls
  imports "Poisson_Homogeneous_Endpoints"
    "HOL-Analysis.Convex"
begin

text \<open>Exact PoissonEndpoints endpoint-hull and real-weight slice
at source commit 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.
The exponent-point definition is the source NewtonRoofSupport.exponentPoint
under the established exponent-pair representation.\<close>

definition exponent_point :: "nat\<times>nat \<Rightarrow> real\<times>real" where
  "exponent_point u=(of_nat(fst u),of_nat(snd u))"
definition real_weight :: "int \<Rightarrow> int \<Rightarrow> nat\<times>nat \<Rightarrow> real" where
  "real_weight rho sigma u= of_int rho* of_nat(fst u)+ of_int sigma* of_nat(snd u)"
definition real_perp_weight :: "int \<Rightarrow> int \<Rightarrow> nat\<times>nat \<Rightarrow> real" where
  "real_perp_weight rho sigma u= of_int sigma* of_nat(fst u)- of_int rho* of_nat(snd u)"
definition point_weight :: "int \<Rightarrow> int \<Rightarrow> real\<times>real \<Rightarrow> real" where
  "point_weight rho sigma z= of_int rho*fst z+ of_int sigma*snd z"
definition point_perp_weight :: "int \<Rightarrow> int \<Rightarrow> real\<times>real \<Rightarrow> real" where
  "point_perp_weight rho sigma z= of_int sigma*fst z- of_int rho*snd z"

lemma real_weight_eq_cast:
  "real_weight rho sigma u= of_int(pair_weight rho sigma u)"
  by (simp add: real_weight_def pair_weight_def algebra_simps)
lemma real_perp_weight_eq_cast:
  "real_perp_weight rho sigma u= of_int(pair_weight sigma (-rho) u)"
  by (simp add: real_perp_weight_def pair_weight_def algebra_simps)
lemma point_weight_exponent_point [simp]:
  "point_weight rho sigma (exponent_point u)=real_weight rho sigma u"
  by (simp add: point_weight_def exponent_point_def real_weight_def)
lemma point_perp_weight_exponent_point [simp]:
  "point_perp_weight rho sigma (exponent_point u)=real_perp_weight rho sigma u"
  by (simp add: point_perp_weight_def exponent_point_def real_perp_weight_def)
lemma point_weight_linear_combination:
  "point_weight rho sigma (a *\<^sub>R z+b *\<^sub>R z')=
    a*point_weight rho sigma z+b*point_weight rho sigma z'"
  by (simp add: point_weight_def algebra_simps)
lemma point_perp_weight_linear_combination:
  "point_perp_weight rho sigma (a *\<^sub>R z+b *\<^sub>R z')=
    a*point_perp_weight rho sigma z+b*point_perp_weight rho sigma z'"
  by (simp add: point_perp_weight_def algebra_simps)

lemma endpoint_point_eq_of_weights_eq_of_perp_eq:
  fixes rho sigma :: int and z z' :: "real\<times>real"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and original: "point_weight rho sigma z=point_weight rho sigma z'"
    and perpendicular: "point_perp_weight rho sigma z=point_perp_weight rho sigma z'"
  shows "z=z'"
proof -
  let ?a = "of_int rho::real"
  let ?b = "of_int sigma::real"
  let ?dx = "fst z-fst z'"
  let ?dy = "snd z-snd z'"
  have first: "?a*?dx+?b*?dy=0"
    using original by (simp add: point_weight_def algebra_simps; linarith)
  have second: "?b*?dx-?a*?dy=0"
    using perpendicular by (simp add: point_perp_weight_def algebra_simps; linarith)
  have dx: "(?a*?a+?b*?b)*?dx=0"
  proof -
    have "(?a*?a+?b*?b)*?dx=?a*(?a*?dx+?b*?dy)+?b*(?b*?dx-?a*?dy)"
      by (simp add: algebra_simps)
    then show ?thesis using first second by simp
  qed
  have dy: "(?a*?a+?b*?b)*?dy=0"
  proof -
    have "(?a*?a+?b*?b)*?dy=?b*(?a*?dx+?b*?dy)-?a*(?b*?dx-?a*?dy)"
      by (simp add: algebra_simps)
    then show ?thesis using first second by simp
  qed
  have square_nonzero: "?a*?a+?b*?b\<noteq>0"
    using nonzero by (simp add: sum_squares_eq_zero_iff)
  have fst_eq: "fst z=fst z'" using dx square_nonzero by auto
  have snd_eq: "snd z=snd z'" using dy square_nonzero by auto
  show ?thesis using fst_eq snd_eq by (simp add: prod_eq_iff)
qed

lemma homogeneous_support_exponent_mem_endpoint_hull:
  fixes rho sigma degree :: int and p :: "complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and homogeneous: "\<And>u. u\<in>biv_support p \<Longrightarrow> pair_weight rho sigma u=degree"
    and high: "dhi\<in>biv_support p" and low: "dlo\<in>biv_support p"
    and maximum: "\<And>u. u\<in>biv_support p \<Longrightarrow>
      pair_weight sigma (-rho) u\<le>pair_weight sigma (-rho) dhi"
    and minimum: "\<And>u. u\<in>biv_support p \<Longrightarrow>
      pair_weight sigma (-rho) dlo\<le>pair_weight sigma (-rho) u"
    and x: "x\<in>biv_support p"
  shows "exponent_point x\<in>convex hull {exponent_point dhi,exponent_point dlo}"
proof -
  have original_weight: "real_weight rho sigma u= of_int degree"
    if "u\<in>biv_support p" for u
    using homogeneous[OF that] by (simp add: real_weight_eq_cast)
  have upper: "real_perp_weight rho sigma x\<le>real_perp_weight rho sigma dhi"
    using maximum[OF x] by (simp add: real_perp_weight_eq_cast)
  have lower: "real_perp_weight rho sigma dlo\<le>real_perp_weight rho sigma x"
    using minimum[OF x] by (simp add: real_perp_weight_eq_cast)
  have ordered: "real_perp_weight rho sigma dlo\<le>real_perp_weight rho sigma dhi"
    using maximum[OF low] by (simp add: real_perp_weight_eq_cast)
  show ?thesis
  proof (cases "real_perp_weight rho sigma dhi=real_perp_weight rho sigma dlo")
    case True
    have real_equal: "real_perp_weight rho sigma x=real_perp_weight rho sigma dhi"
      using upper lower True by arith
    have perp_equal: "pair_weight sigma (-rho) x=pair_weight sigma (-rho) dhi"
      using real_equal by (simp add: real_perp_weight_eq_cast)
    have original_equal: "pair_weight rho sigma x=pair_weight rho sigma dhi"
      using homogeneous[OF x] homogeneous[OF high] by simp
    have equal: "x=dhi"
      by (rule exponent_eq_of_weights_eq_of_perp_eq[OF nonzero original_equal perp_equal])
    have "exponent_point dhi\<in>convex hull {exponent_point dhi,exponent_point dlo}"
      by (rule hull_inc) simp
    then show ?thesis using equal by simp
  next
    case False
    let ?H = "real_perp_weight rho sigma dhi"
    let ?L = "real_perp_weight rho sigma dlo"
    let ?X = "real_perp_weight rho sigma x"
    let ?t = "(?X-?L)/(?H-?L)"
    let ?z = "?t *\<^sub>R exponent_point dhi+(1-?t) *\<^sub>R exponent_point dlo"
    have strict: "?L<?H" using ordered False by arith
    have denominator: "0<?H-?L" using strict by arith
    have denominator_nonzero: "?H-?L\<noteq>0" using denominator by arith
    have t_nonnegative: "0\<le>?t"
      by (rule divide_nonneg_pos) (use lower denominator in auto)
    have t_le_one: "?t\<le>1"
      using upper denominator by (simp add: divide_le_eq)
    have denominator_times_t: "(?H-?L)*?t=?X-?L"
      using denominator_nonzero by simp
    have interpolation: "?X=?t*?H+(1-?t)*?L"
      using denominator_times_t by algebra
    have z_original: "point_weight rho sigma ?z= of_int degree"
      by (simp only: point_weight_linear_combination point_weight_exponent_point
        original_weight[OF high] original_weight[OF low]) (simp add: algebra_simps)
    have z_perpendicular: "point_perp_weight rho sigma ?z=?X"
      using interpolation by (simp only: point_perp_weight_linear_combination point_perp_weight_exponent_point)
    have points_equal: "exponent_point x=?z"
    proof (rule endpoint_point_eq_of_weights_eq_of_perp_eq[OF nonzero])
      show "point_weight rho sigma (exponent_point x)=point_weight rho sigma ?z"
        using original_weight[OF x] z_original by simp
      show "point_perp_weight rho sigma (exponent_point x)=point_perp_weight rho sigma ?z"
        using z_perpendicular by simp
    qed
    have z_in_hull: "?z\<in>convex hull {exponent_point dhi,exponent_point dlo}"
      unfolding convex_hull_2
      by (rule CollectI, rule exI[of _ ?t], rule exI[of _ "1-?t"])
        (use t_nonnegative t_le_one in auto)
    show ?thesis using points_equal z_in_hull by simp
  qed
qed

end
