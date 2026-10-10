theory One_Sided_Symbol_Face_Adapters
  imports "One_Sided_Grade_Basic"
    "One_Sided_Ratios"
begin

text \<open>Source-exact integer symbol/face producer slice for
OneSidedFaceDispatch at 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.
Native PBW support already uses the coordinate pairs that the source obtains
by imaging its exponent support. No exact-pair dispatch result is assumed.\<close>

definition one_sided_symbol_coords :: "complex poly_operator \<Rightarrow> (nat\<times>nat) set" where
  "one_sided_symbol_coords T=biv_support (pbw_symbol T)"

lemma one_sided_symbol_coords_strict:
  assumes "\<forall>u\<in>biv_support (pbw_symbol T). pair_grade u<0"
  shows "\<forall>u\<in>one_sided_symbol_coords T. fst u<snd u"
  using assms by (auto simp: one_sided_symbol_coords_def pair_grade_def)

lemma one_sided_symbol_support_face_dichotomy:
  fixes T :: "complex poly_operator"
  assumes grade: "\<forall>u\<in>biv_support (pbw_symbol T). pair_grade u<0"
    and other: "\<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1)"
  shows "(\<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1) \<and> snd u=fst u+1) \<or>
    (\<exists>t::rat. \<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1) \<and>
      0\<le>t \<and> t<1 \<and> of_nat(fst u)=t*(of_nat(snd u)-1) \<and>
      (\<forall>v\<in>biv_support (pbw_symbol T). of_nat(fst v)\<le>t*(of_nat(snd v)-1)))"
proof -
  have strict: "\<forall>u\<in>biv_support (pbw_symbol T). fst u<snd u"
    using grade by (auto simp: pair_grade_def)
  show ?thesis by (rule one_sided_support_face_dichotomy[OF finite_biv_support strict other])
qed

lemma symbol_v_degree_max:
  assumes u: "u\<in>biv_support (pbw_symbol T)"
  shows "v_degree rho sigma T=Max (pair_weight rho sigma ` biv_support (pbw_symbol T))"
  using u by (auto simp: v_degree_def weighted_degree_def)

lemma symbol_weight_le_v_degree:
  assumes u: "u\<in>biv_support (pbw_symbol T)"
  shows "pair_weight rho sigma u\<le>v_degree rho sigma T"
  unfolding symbol_v_degree_max[OF u]
  by (rule Max_ge) (use u in auto)

lemma symbol_maximizer_mem_leading_form:
  assumes u: "u\<in>biv_support (pbw_symbol T)"
    and top: "\<And>v. v\<in>biv_support (pbw_symbol T) \<Longrightarrow>
      pair_weight rho sigma v\<le>pair_weight rho sigma u"
  shows "u\<in>biv_support (leading_form rho sigma T)"
proof -
  have maximum: "Max (pair_weight rho sigma ` biv_support (pbw_symbol T))=pair_weight rho sigma u"
    by (rule Max_eqI) (use u top in auto)
  show ?thesis using u maximum
    by (simp add: leading_form_def weighted_component_support symbol_v_degree_max[OF u])
qed

lemma one_sided_symbol_grade_minus_one_mem_face:
  fixes T :: "complex poly_operator"
  assumes grade: "\<forall>v\<in>biv_support (pbw_symbol T). pair_grade v<0"
    and u: "u\<in>biv_support (pbw_symbol T)" and ug: "pair_grade u=-1"
  shows "u\<in>biv_support (leading_form 1 (-1) T)"
proof (rule symbol_maximizer_mem_leading_form[OF u])
  fix v assume v: "v\<in>biv_support (pbw_symbol T)"
  have "pair_grade v\<le>-1" using grade v by auto
  then show "pair_weight 1 (-1) v\<le>pair_weight 1 (-1) u"
    using ug by (simp add: pair_grade_def pair_weight_def)
qed

lemma leading_form_eq_of_support_eq:
  assumes "biv_support (leading_form rho sigma T)=biv_support (leading_form r s T)"
  shows "leading_form rho sigma T=leading_form r s T"
proof (rule biv_eqI)
  fix i j
  have members: "((i,j)\<in>biv_support (leading_form rho sigma T)) =
    ((i,j)\<in>biv_support (leading_form r s T))"
    using assms by simp
  have nonzero: "(biv_coeff (leading_form rho sigma T) i j\<noteq>0) =
    (biv_coeff (leading_form r s T) i j\<noteq>0)"
    using members by (simp only: biv_support_def mem_Collect_eq fst_conv snd_conv)
  show "biv_coeff (leading_form rho sigma T) i j=biv_coeff (leading_form r s T) i j"
    using nonzero by (auto simp only: leading_form_def weighted_component_coeff
      split: if_splits)
qed

lemma leading_form_degree_of_y_term:
  assumes "(0,1)\<in>biv_support (leading_form (int ell) (-int d) T)"
  shows "v_degree (int ell) (-int d) T=-int d"
  using assms by (simp add: leading_form_def weighted_component_support pair_weight_def)

lemma leading_form_degree_of_x_term:
  assumes "(1,0)\<in>biv_support (leading_form (int ell) (-int d) T)"
  shows "v_degree (int ell) (-int d) T=int ell"
  using assms by (simp add: leading_form_def weighted_component_support pair_weight_def)

lemma positive_grade_positive_crossing_weight:
  fixes rho sigma :: int
  assumes rho: "0<rho" and sum: "0<rho+sigma" and grade: "0<pair_grade u"
  shows "0<pair_weight rho sigma u"
proof -
  have gap: "0<int(fst u)-int(snd u)" using grade by (simp add: pair_grade_def)
  have first: "0<rho*(int(fst u)-int(snd u))" by (rule mult_pos_pos[OF rho gap])
  have rest: "0\<le>(rho+sigma)*int(snd u)" by (rule mult_nonneg_nonneg) (use sum in auto)
  have weight: "pair_weight rho sigma u=rho*(int(fst u)-int(snd u))+(rho+sigma)*int(snd u)"
    by (simp add: pair_weight_def algebra_simps)
  show ?thesis using first rest by (simp add: weight)
qed

lemma positive_grade_forces_positive_crossing_v_degree:
  fixes T :: "complex poly_operator"
  assumes rho: "0<rho" and sum: "0<rho+sigma"
    and positive: "\<exists>u\<in>biv_support (pbw_symbol T). 0<pair_grade u"
  shows "0<v_degree rho sigma T"
proof -
  obtain u where u: "u\<in>biv_support (pbw_symbol T)" and grade: "0<pair_grade u"
    using positive by blast
  have "0<pair_weight rho sigma u" by (rule positive_grade_positive_crossing_weight[OF rho sum grade])
  also have "pair_weight rho sigma u\<le>v_degree rho sigma T"
    by (rule symbol_weight_le_v_degree[OF u])
  finally show ?thesis .
qed

lemma one_sided_symbol_face_normal_sign:
  fixes T :: "complex poly_operator" and rho sigma :: int
  assumes strict: "\<forall>u\<in>biv_support (pbw_symbol T). pair_grade u<0"
    and sum: "0<rho+sigma"
    and gen: "(0,1)\<in>biv_support (leading_form rho sigma T)"
    and u: "u\<in>biv_support (leading_form rho sigma T)" and ne: "u\<noteq>(0,1)"
  shows "0<rho \<and> sigma\<le>0 \<and> fst u+1<snd u"
proof -
  have full: "u\<in>biv_support (pbw_symbol T)" using leading_support_subset u by blast
  have grade: "fst u<snd u" using strict full by (auto simp: pair_grade_def)
  have gen_weight: "sigma=v_degree rho sigma T"
    using gen by (simp add: leading_form_def weighted_component_support pair_weight_def)
  have u_weight: "pair_weight rho sigma u=v_degree rho sigma T"
    using u by (simp add: leading_form_def weighted_component_support)
  have weight: "rho*int(fst u)+sigma*int(snd u)=sigma"
    using u_weight gen_weight by (simp add: pair_weight_def mult.commute)
  show ?thesis by (rule one_sided_two_point_normal_sign[OF sum grade ne weight])
qed

end
