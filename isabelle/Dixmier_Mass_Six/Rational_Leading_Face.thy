theory Rational_Leading_Face
 imports "Finite_First_Upward_Tilt"
   "Weighted_Newton_Definitions"
begin

definition rationalNewtonWeight::"rat \<Rightarrow> (nat\<times>nat) \<Rightarrow> rat" where
 "rationalNewtonWeight t a=of_nat(fst a)+t*of_nat(snd a)"

lemma leadingForm_mem_iff_rational_slope:
 fixes P::"complex poly_operator" and rho sigma::int
 assumes positive: "0<rho"
 shows "a\<in>biv_support(leading_form rho sigma P) \<longleftrightarrow>
   a\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>b\<in>biv_support(pbw_symbol P).
     rationalNewtonWeight (of_int sigma/of_int rho) b\<le>
     rationalNewtonWeight (of_int sigma/of_int rho) a)"
proof -
 let ?S="biv_support(pbw_symbol P)"
 let ?t="(of_int sigma/of_int rho::rat)"
 have rho: "(0::rat)<of_int rho" using positive by simp
 have scale: "(of_int(pair_weight rho sigma x)::rat)=of_int rho*rationalNewtonWeight ?t x" for x
   using positive by (simp add: pair_weight_def rationalNewtonWeight_def algebra_simps)
 have order: "pair_weight rho sigma x\<le>pair_weight rho sigma y \<longleftrightarrow>
   rationalNewtonWeight ?t x\<le>rationalNewtonWeight ?t y" for x y
 proof -
   have cast: "pair_weight rho sigma x\<le>pair_weight rho sigma y \<longleftrightarrow>
     (of_int(pair_weight rho sigma x)::rat)\<le>of_int(pair_weight rho sigma y)" by simp
   show ?thesis by (simp only: cast scale mult_le_cancel_left_pos[OF rho])
 qed
 show ?thesis
 proof
   assume face: "a\<in>biv_support(leading_form rho sigma P)"
   have raw: "a\<in>?S" and weight: "pair_weight rho sigma a=v_degree rho sigma P"
     using face by (auto simp: leading_form_def weighted_component_support)
   have nonempty: "?S\<noteq>{}" using raw by blast
   have maximum: "v_degree rho sigma P=Max(pair_weight rho sigma ` ?S)"
     using nonempty by (simp add: v_degree_def weighted_degree_def)
   have upper: "pair_weight rho sigma b\<le>pair_weight rho sigma a" if "b\<in>?S" for b
     unfolding weight maximum by (rule Max_ge) (simp, rule imageI[OF that])
   show "a\<in>?S \<and> (\<forall>b\<in>?S. rationalNewtonWeight ?t b\<le>rationalNewtonWeight ?t a)"
     using raw upper by (simp only: order; blast)
 next
   assume maximizer: "a\<in>?S \<and> (\<forall>b\<in>?S. rationalNewtonWeight ?t b\<le>rationalNewtonWeight ?t a)"
   have raw: "a\<in>?S" using maximizer by blast
   have nonempty: "?S\<noteq>{}" using raw by blast
   have upper: "pair_weight rho sigma b\<le>pair_weight rho sigma a" if "b\<in>?S" for b
     using maximizer that by (simp only: order; blast)
   have member: "pair_weight rho sigma a\<in>pair_weight rho sigma ` ?S" by (rule imageI[OF raw])
   have maximum: "Max(pair_weight rho sigma ` ?S)=pair_weight rho sigma a"
     by (rule Max_eqI) (simp, use upper in auto, rule member)
   have weight: "pair_weight rho sigma a=v_degree rho sigma P"
     using nonempty maximum by (simp add: v_degree_def weighted_degree_def)
   show "a\<in>biv_support(leading_form rho sigma P)"
     using raw weight by (simp add: leading_form_def weighted_component_support)
 qed
qed

lemma leadingFace_exists_first_upward_tilt:
 fixes P::"complex poly_operator" and rho sigma::int
 assumes rho: "0<rho" and a: "a\<in>biv_support(leading_form rho sigma P)"
   and last: "\<And>p. p\<in>biv_support(leading_form rho sigma P) \<Longrightarrow> snd p\<le>snd a"
   and above: "\<exists>p\<in>biv_support(pbw_symbol P). snd a<snd p"
 shows "\<exists>t::rat. of_int sigma/of_int rho<t \<and>
   (\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a) \<and>
   (\<exists>b\<in>biv_support(pbw_symbol P). snd a<snd b \<and>
     rationalNewtonWeight t b=rationalNewtonWeight t a)"
proof -
 let ?S="biv_support(pbw_symbol P)"
 let ?t="(of_int sigma/of_int rho::rat)"
 let ?w="rationalNewtonWeight ?t"
 have data: "a\<in>?S \<and> (\<forall>p\<in>?S. ?w p\<le>?w a)"
   by (rule iffD1[OF leadingForm_mem_iff_rational_slope[OF rho] a])
 have top: "?w p\<le>?w a" if "p\<in>?S" for p using data that by blast
 have endpt: "snd p\<le>snd a" if p: "p\<in>?S" and equal: "?w p=?w a" for p
 proof -
   have max: "\<forall>b\<in>?S. ?w b\<le>?w p" using top equal by simp
   have face: "p\<in>biv_support(leading_form rho sigma P)"
     by (simp only: leadingForm_mem_iff_rational_slope[OF rho]; rule conjI[OF p max])
   show ?thesis by (rule last[OF face])
 qed
 obtain delta B where positive: "0<delta"
   and bound: "\<forall>p\<in>?S. ?w p+delta*of_nat(snd p)\<le>?w a+delta*of_nat(snd a)"
   and B: "B\<in>?S" and higher: "snd a<snd B"
   and tie: "?w B+delta*of_nat(snd B)=?w a+delta*of_nat(snd a)"
   using finiteSupport_exists_first_upward_tilt[where S="?S" and y=snd and w="?w" and V="?w a" and M="snd a",
     OF finite_biv_support top endpt above] by blast
 have shift: "rationalNewtonWeight (?t+delta) p=?w p+delta*of_nat(snd p)" for p
   by (simp add: rationalNewtonWeight_def algebra_simps)
 show ?thesis by (intro exI[of _ "?t+delta"])
   (use positive bound B higher tie in \<open>simp only: shift; auto\<close>)
qed

end
