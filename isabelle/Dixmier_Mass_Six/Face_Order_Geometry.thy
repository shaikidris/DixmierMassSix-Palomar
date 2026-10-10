theory Face_Order_Geometry
 imports "Weighted_Newton_Definitions"
begin

definition real_newton_weight::"real \<Rightarrow> real \<Rightarrow> (nat\<times>nat) \<Rightarrow> real" where
 "real_newton_weight rho sigma a=rho*of_nat(fst a)+sigma*of_nat(snd a)"
definition real_exposed_face::"real \<Rightarrow> real \<Rightarrow> (nat\<times>nat) set \<Rightarrow> (nat\<times>nat) set" where
 "real_exposed_face rho sigma S={a\<in>S. \<forall>b\<in>S. real_newton_weight rho sigma b\<le>real_newton_weight rho sigma a}"

lemma real_exposed_points_ordered:
 fixes S::"(nat\<times>nat) set" and t1 t2::real
 assumes slope: "t1<t2" and a: "a\<in>real_exposed_face 1 t1 S"
   and b: "b\<in>real_exposed_face 1 t2 S"
 shows "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
proof -
 have ab: "of_nat(fst b)+t1*of_nat(snd b)\<le>of_nat(fst a)+t1*of_nat(snd a)"
   and ba: "of_nat(fst a)+t2*of_nat(snd a)\<le>of_nat(fst b)+t2*of_nat(snd b)"
   using a b by (auto simp: real_exposed_face_def real_newton_weight_def)
 have order: "(of_nat(snd a)::real)\<le>of_nat(snd b)"
 proof (rule ccontr)
   assume "\<not>(of_nat(snd a)::real)\<le>of_nat(snd b)"
   then have reverse: "(of_nat(snd b)::real)<of_nat(snd a)" by simp
   have positive: "0<(t2-t1)*(of_nat(snd a)-of_nat(snd b))"
     by (rule mult_pos_pos) (use slope reverse in auto)
   show False using positive ab ba by (simp add: algebra_simps; linarith)
 qed
 have same: "a=b" if y: "snd a=snd b"
 proof -
   have x: "fst a=fst b" using ab ba y by simp
   show ?thesis using x y by (simp add: prod_eq_iff)
 qed
 show ?thesis using order same by auto
qed

lemma leadingForm_mem_normalized_real_face:
 fixes P::"complex poly_operator" and rho sigma::int and a::"nat\<times>nat"
 assumes rho: "0<rho"
 shows "a\<in>biv_support(leading_form rho sigma P) \<longleftrightarrow>
   a\<in>real_exposed_face 1 (of_int sigma/of_int rho) (biv_support(pbw_symbol P))"
proof -
 let ?S="biv_support(pbw_symbol P)"
 have positive: "(0::real)<of_int rho" using rho by simp
 have scale: "(of_int(pair_weight rho sigma x)::real)=
   of_int rho*real_newton_weight 1 (of_int sigma/of_int rho) x" for x
   using rho by (simp add: pair_weight_def real_newton_weight_def algebra_simps)
 have order: "pair_weight rho sigma x\<le>pair_weight rho sigma y \<longleftrightarrow>
   real_newton_weight 1 (of_int sigma/of_int rho) x\<le>real_newton_weight 1 (of_int sigma/of_int rho) y" for x y
 proof -
   have cast: "pair_weight rho sigma x\<le>pair_weight rho sigma y \<longleftrightarrow>
     (of_int(pair_weight rho sigma x)::real)\<le>of_int(pair_weight rho sigma y)" by simp
   show ?thesis by (simp only: cast scale mult_le_cancel_left_pos[OF positive])
 qed
 have integer_max: "a\<in>biv_support(leading_form rho sigma P) \<longleftrightarrow>
   a\<in>?S \<and> (\<forall>b\<in>?S. pair_weight rho sigma b\<le>pair_weight rho sigma a)"
 proof
   assume face: "a\<in>biv_support(leading_form rho sigma P)"
   have raw: "a\<in>?S" and weight: "pair_weight rho sigma a=v_degree rho sigma P"
     using face by (auto simp: leading_form_def weighted_component_support)
   have nonempty: "?S\<noteq>{}" using raw by blast
   have maximum: "v_degree rho sigma P=Max(pair_weight rho sigma ` ?S)"
     using nonempty by (simp add: v_degree_def weighted_degree_def)
   have upper: "pair_weight rho sigma b\<le>pair_weight rho sigma a" if "b\<in>?S" for b
     unfolding weight maximum by (rule Max_ge) (simp, rule imageI[OF that])
   show "a\<in>?S \<and> (\<forall>b\<in>?S. pair_weight rho sigma b\<le>pair_weight rho sigma a)"
     using raw upper by blast
 next
   assume data: "a\<in>?S \<and> (\<forall>b\<in>?S. pair_weight rho sigma b\<le>pair_weight rho sigma a)"
   have raw: "a\<in>?S" and upper: "\<And>b. b\<in>?S \<Longrightarrow> pair_weight rho sigma b\<le>pair_weight rho sigma a" using data by blast+
   have member: "pair_weight rho sigma a\<in>pair_weight rho sigma ` ?S" by (rule imageI[OF raw])
   have maximum: "Max(pair_weight rho sigma ` ?S)=pair_weight rho sigma a"
     by (rule Max_eqI) (simp, use upper in auto, rule member)
   have nonempty: "?S\<noteq>{}" using raw by blast
   have weight: "pair_weight rho sigma a=v_degree rho sigma P"
     using nonempty maximum by (simp add: v_degree_def weighted_degree_def)
   show "a\<in>biv_support(leading_form rho sigma P)"
     using raw weight by (simp add: leading_form_def weighted_component_support)
 qed
 show ?thesis by (simp only: integer_max real_exposed_face_def mem_Collect_eq order)
qed

lemma leadingFace_points_ordered_by_slope:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and slope: "(of_int sigma1/of_int rho1::real)<of_int sigma2/of_int rho2"
   and a: "a\<in>biv_support(leading_form rho1 sigma1 P)"
   and b: "b\<in>biv_support(leading_form rho2 sigma2 P)"
 shows "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
 by (rule real_exposed_points_ordered[OF slope])
   (use a b in \<open>simp_all only: leadingForm_mem_normalized_real_face[OF rho1] leadingForm_mem_normalized_real_face[OF rho2]\<close>)
end
