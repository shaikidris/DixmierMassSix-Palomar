theory One_Sided_Integer_Face
  imports "One_Sided_Symbol_Face_Adapters"
    "HOL.Rat"
begin

text \<open>Exact source conclusions from OneSidedFaceDispatch at
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. The rational supporting line
already produced by the checked finite-support theorem is cleared using its
positive denominator. This directly constructs the same required integer
face, without replacing any exact-pair producer by a premise.\<close>

lemma one_sided_symbol_strict_line_to_integer_face:
  fixes T :: "complex poly_operator" and t :: rat
  assumes gen: "(0,1)\<in>biv_support (pbw_symbol T)"
    and u: "u\<in>biv_support (pbw_symbol T)" and ne: "u\<noteq>(0,1)"
    and less: "t<1"
    and on_line: "of_nat(fst u)=t*(of_nat(snd u)-1)"
    and line: "\<forall>v\<in>biv_support (pbw_symbol T).
      of_nat(fst v)\<le>t*(of_nat(snd v)-1)"
  shows "\<exists>rho sigma::int. 0<rho+sigma \<and>
    (0,1)\<in>biv_support (leading_form rho sigma T) \<and>
    u\<in>biv_support (leading_form rho sigma T)"
proof -
  obtain a b where quotient: "quotient_of t=(a,b)" by (cases "quotient_of t") auto
  have b_positive: "0<b" by (rule quotient_of_denom_pos[OF quotient])
  have b_rat_positive: "0<(of_int b::rat)" using b_positive by simp
  have t_quotient: "t=of_int a/of_int b" by (rule quotient_of_div[OF quotient])
  have bt: "(of_int b::rat)*t=of_int a"
    using b_positive by (simp add: t_quotient)
  have a_less_b_rat: "(of_int a::rat)<of_int b"
    using less b_positive by (simp add: t_quotient divide_less_eq)
  have a_less_b: "a<b" using a_less_b_rat by simp
  have positive_sum: "0<b+(-a)" using a_less_b by arith
  have integer_line: "b*int(fst v)\<le>a*(int(snd v)-1)"
    if v: "v\<in>biv_support (pbw_symbol T)" for v
  proof -
    have scaled: "(of_int b::rat)*of_nat(fst v)\<le>of_int b*(t*(of_nat(snd v)-1))"
      by (rule mult_left_mono) (use line v b_rat_positive in auto)
    have rational_line: "(of_int b::rat)*of_nat(fst v)\<le>of_int a*(of_nat(snd v)-1)"
      using scaled by (simp only: mult.assoc[symmetric] bt)
    have cast: "(of_int (b*int(fst v))::rat)\<le>of_int (a*(int(snd v)-1))"
      using rational_line by simp
    show ?thesis using cast by (simp only: of_int_le_iff)
  qed
  have integer_on_line: "b*int(fst u)=a*(int(snd u)-1)"
  proof -
    have scaled: "(of_int b::rat)*of_nat(fst u)=of_int b*(t*(of_nat(snd u)-1))"
      using on_line by simp
    have rational_eq: "(of_int b::rat)*of_nat(fst u)=of_int a*(of_nat(snd u)-1)"
      using scaled by (simp only: mult.assoc[symmetric] bt)
    have cast: "(of_int (b*int(fst u))::rat)=of_int (a*(int(snd u)-1))"
      using rational_eq by simp
    show ?thesis using cast by (simp only: of_int_eq_iff)
  qed
  have bounds: "pair_weight b (-a) v\<le>-a"
    if "v\<in>biv_support (pbw_symbol T)" for v
    using integer_line[OF that] by (simp add: pair_weight_def algebra_simps)
  have u_weight: "pair_weight b (-a) u=-a"
    using integer_on_line by (simp add: pair_weight_def algebra_simps)
  have gen_face: "(0,1)\<in>biv_support (leading_form b (-a) T)"
    by (rule symbol_maximizer_mem_leading_form[OF gen])
      (use bounds in \<open>simp add: pair_weight_def\<close>)
  have u_face: "u\<in>biv_support (leading_form b (-a) T)"
    by (rule symbol_maximizer_mem_leading_form[OF u]) (use bounds u_weight in auto)
  show ?thesis using positive_sum gen_face u_face by blast
qed

lemma one_sided_symbol_face_dispatch:
  fixes T :: "complex poly_operator"
  assumes grade: "\<forall>u\<in>biv_support (pbw_symbol T). pair_grade u<0"
    and gen: "(0,1)\<in>biv_support (pbw_symbol T)"
    and other: "\<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1)"
  shows "(\<exists>u\<in>biv_support (leading_form 1 (-1) T). u\<noteq>(0,1) \<and>
      (0,1)\<in>biv_support (leading_form 1 (-1) T)) \<or>
    (\<exists>rho sigma::int. 0<rho+sigma \<and>
      (0,1)\<in>biv_support (leading_form rho sigma T) \<and>
      (\<exists>u\<in>biv_support (leading_form rho sigma T). u\<noteq>(0,1)))"
proof -
  note alternatives = one_sided_symbol_support_face_dichotomy[OF grade other]
  then show ?thesis
  proof
    assume boundary: "\<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1) \<and> snd u=fst u+1"
    obtain u where u: "u\<in>biv_support (pbw_symbol T)" and ne: "u\<noteq>(0,1)"
      and boundary_eq: "snd u=fst u+1" using boundary by blast
    have ug: "pair_grade u=-1" by (simp add: pair_grade_def boundary_eq)
    have u_face: "u\<in>biv_support (leading_form 1 (-1) T)"
      by (rule one_sided_symbol_grade_minus_one_mem_face[OF grade u ug])
    have gen_grade: "pair_grade (0,1)=-1" by (simp add: pair_grade_def)
    have gen_face: "(0,1)\<in>biv_support (leading_form 1 (-1) T)"
      by (rule one_sided_symbol_grade_minus_one_mem_face[OF grade gen gen_grade])
    show ?thesis using u_face ne gen_face by blast
  next
    assume strict: "\<exists>t::rat. \<exists>u\<in>biv_support (pbw_symbol T). u\<noteq>(0,1) \<and>
      0\<le>t \<and> t<1 \<and> of_nat(fst u)=t*(of_nat(snd u)-1) \<and>
      (\<forall>v\<in>biv_support (pbw_symbol T). of_nat(fst v)\<le>t*(of_nat(snd v)-1))"
    obtain t u where u: "u\<in>biv_support (pbw_symbol T)" and ne: "u\<noteq>(0,1)"
      and less: "(t::rat)<1" and on_line: "of_nat(fst u)=t*(of_nat(snd u)-1)"
      and line: "\<forall>v\<in>biv_support (pbw_symbol T). of_nat(fst v)\<le>t*(of_nat(snd v)-1)"
      using strict by blast
    obtain rho sigma where sum: "0<rho+sigma"
      and gen_face: "(0,1)\<in>biv_support (leading_form rho sigma T)"
      and u_face: "u\<in>biv_support (leading_form rho sigma T)"
      using one_sided_symbol_strict_line_to_integer_face[OF gen u ne less on_line line] by blast
    show ?thesis using sum gen_face u_face ne by blast
  qed
qed

end
