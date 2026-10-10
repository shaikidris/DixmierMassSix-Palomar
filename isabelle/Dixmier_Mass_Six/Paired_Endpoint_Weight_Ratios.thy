theory Paired_Endpoint_Weight_Ratios
 imports "Negative_Face_Boundaries"
begin

lemma leadingFace_max_y_eq_max_x:
 fixes P::"complex poly_operator" and rho s::nat
 assumes rho: "0<rho" and s: "0<s"
   and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and b: "b\<in>biv_support(leading_form (int rho) (-int s) P)"
   and ay: "snd b\<le>snd a" and bx: "fst a\<le>fst b"
 shows "a=b"
proof -
 have aw: "pair_weight (int rho) (-int s) a=v_degree (int rho) (-int s) P"
   and bw: "pair_weight (int rho) (-int s) b=v_degree (int rho) (-int s) P"
   using a b by (simp_all add: leading_form_def weighted_component_support)
 have equation: "int rho*(int(fst b)-int(fst a))+int s*(int(snd a)-int(snd b))=0"
   using aw bw by (simp add: pair_weight_def algebra_simps; linarith)
 have xp: "0\<le>int rho*(int(fst b)-int(fst a))" using bx by (intro mult_nonneg_nonneg) simp_all
 have yp: "0\<le>int s*(int(snd a)-int(snd b))" using ay by (intro mult_nonneg_nonneg) simp_all
 have xzero: "int rho*(int(fst b)-int(fst a))=0" using equation xp yp by linarith
 have yzero: "int s*(int(snd a)-int(snd b))=0" using equation xp yp by linarith
 have x: "fst a=fst b" using xzero rho by auto
 have y: "snd a=snd b" using yzero s by auto
 show ?thesis using x y by (simp add: prod_eq_iff)
qed

lemma counterexample_negative_face_maxima_proportional:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)"
   and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and b: "b\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and amax: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd e\<le>snd a"
   and bmax: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) Q) \<Longrightarrow> snd e\<le>snd b"
 shows "\<exists>n d::nat. 0<n \<and> 0<d \<and> coprime d n \<and> n*fst a=d*fst b \<and> n*snd a=d*snd b"
proof -
 obtain n d u v r t where n: "0<n" and d: "0<d" and cop: "coprime d n"
   and Pend: "(d*u,d*v)\<in>biv_support(leading_form (int rho) (-int s) P)"
   and Qend: "(n*u,n*v)\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and Pbound: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). d*r\<le>fst e \<and> fst e\<le>d*u"
   and Qbound: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) Q). n*r\<le>fst e \<and> fst e\<le>n*u"
   using counterexample_strict_negative_face_proportional_endpoints[OF pair s direction] by blast
 have ay: "snd(d*u,d*v)\<le>snd a" by (rule amax[OF Pend])
 have ax: "fst a\<le>fst(d*u,d*v)" using Pbound a by auto
 have ae: "a=(d*u,d*v)" by (rule leadingFace_max_y_eq_max_x[OF rho s a Pend ay ax])
 have b_y: "snd(n*u,n*v)\<le>snd b" by (rule bmax[OF Qend])
 have bx: "fst b\<le>fst(n*u,n*v)" using Qbound b by auto
 have be: "b=(n*u,n*v)" by (rule leadingFace_max_y_eq_max_x[OF rho s b Qend b_y bx])
 show ?thesis by (intro exI[of _ n] exI[of _ d])
   (use n d cop in \<open>simp add: ae be mult.assoc mult.commute mult.left_commute\<close>)
qed

lemma paired_face_points_common_weight_ratio:
 fixes P Q::"complex poly_operator" and n d::nat
   and rho1 sigma1 rho2 sigma2::int and a b::"nat \<times> nat"
 assumes a1: "a\<in>biv_support(leading_form rho1 sigma1 P)"
   and a2: "a\<in>biv_support(leading_form rho2 sigma2 P)"
   and b1: "b\<in>biv_support(leading_form rho1 sigma1 Q)"
   and b2: "b\<in>biv_support(leading_form rho2 sigma2 Q)"
   and x: "n*fst a=d*fst b" and y: "n*snd a=d*snd b"
 shows "v_degree rho1 sigma1 P*int n=v_degree rho1 sigma1 Q*int d \<and>
   v_degree rho2 sigma2 P*int n=v_degree rho2 sigma2 Q*int d"
proof -
 have aweight: "pair_weight rho sigma a=v_degree rho sigma P"
   if "a\<in>biv_support(leading_form rho sigma P)" for rho sigma
   using that by (simp add: leading_form_def weighted_component_support)
 have bweight: "pair_weight rho sigma b=v_degree rho sigma Q"
   if "b\<in>biv_support(leading_form rho sigma Q)" for rho sigma
   using that by (simp add: leading_form_def weighted_component_support)
 have xi: "int n*int(fst a)=int d*int(fst b)" using x by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
 have yi: "int n*int(snd a)=int d*int(snd b)" using y by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
 have proportional: "pair_weight rho sigma a*int n=pair_weight rho sigma b*int d" for rho sigma
 proof -
   have "pair_weight rho sigma a*int n = rho*(int n*int(fst a))+sigma*(int n*int(snd a))"
     by (simp add: pair_weight_def algebra_simps)
   also have "...=rho*(int d*int(fst b))+sigma*(int d*int(snd b))" by (simp only: xi yi)
   also have "...=pair_weight rho sigma b*int d" by (simp add: pair_weight_def algebra_simps)
   finally show ?thesis .
 qed
 show ?thesis using proportional[of rho1 sigma1] proportional[of rho2 sigma2]
   by (simp only: aweight[OF a1] aweight[OF a2] bweight[OF b1] bweight[OF b2])
qed

lemma counterexample_paired_last_negative_meets_horizontal:
 fixes P Q::"complex poly_operator" and rho s j::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)"
   and index: "j+1=length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
   and face: "in_direction (int rho) (-int s) P"
 shows "\<exists>a b. \<exists>n d::nat.
 a\<in>biv_support(leading_form (int rho) (-int s) P) \<and> a\<in>biv_support(leading_form 1 0 P) \<and>
 b\<in>biv_support(leading_form (int rho) (-int s) Q) \<and> b\<in>biv_support(leading_form 1 0 Q) \<and>
 0<n \<and> 0<d \<and> coprime d n \<and> n*fst a=d*fst b \<and> n*snd a=d*snd b"
proof -
 obtain a where aN: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and aH: "a\<in>biv_support(leading_form 1 0 P)"
   and amax: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd e\<le>snd a"
   using counterexample_last_negative_face_meets_horizontal[OF pair rho s direction index entry face] by blast
 have negative: "-int s<0" using s by simp
 have faceQ: "in_direction (int rho) (-int s) Q"
   using counterexample_strict_negative_InDir_iff[OF pair direction negative] face by blast
 have lists: "ggv_ordered_negative_face_slopes P=ggv_ordered_negative_face_slopes Q"
   by (rule ggv_ordered_negative_slopes_eq[OF pair])
 have indexQ: "j+1=length(ggv_ordered_negative_face_slopes Q)" using index by (simp only: lists)
 have entryQ: "ggv_ordered_negative_face_slopes Q!j=(of_int(-int s)/ of_int(int rho)::rat)" using entry by (simp only: lists)
 obtain b where bN: "b\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and bH: "b\<in>biv_support(leading_form 1 0 Q)"
   and bmax: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) Q) \<Longrightarrow> snd e\<le>snd b"
   using counterexample_last_negative_face_meets_horizontal[OF isCounterexamplePair_swap_neg[OF pair] rho s direction indexQ entryQ faceQ] by blast
 obtain n d where n: "0<n" and d: "0<d" and cop: "coprime d n" and x: "n*fst a=d*fst b" and y: "n*snd a=d*snd b"
   using counterexample_negative_face_maxima_proportional[OF pair rho s direction aN bN amax bmax] by blast
 show ?thesis using aN aH bN bH n d cop x y by blast
qed

lemma counterexample_last_negative_horizontal_common_weight_ratio:
 fixes P Q::"complex poly_operator" and rho s j::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)"
   and index: "j+1=length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
   and face: "in_direction (int rho) (-int s) P"
 shows "\<exists>n d::nat. 0<n \<and> 0<d \<and> coprime d n \<and>
 v_degree (int rho) (-int s) P*int n=v_degree (int rho) (-int s) Q*int d \<and>
 v_degree 1 0 P*int n=v_degree 1 0 Q*int d"
proof -
 obtain a b n d where aN: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and aH: "a\<in>biv_support(leading_form 1 0 P)"
   and bN: "b\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and bH: "b\<in>biv_support(leading_form 1 0 Q)"
   and n: "0<n" and d: "0<d" and cop: "coprime d n"
   and x: "n*fst a=d*fst b" and y: "n*snd a=d*snd b"
   using counterexample_paired_last_negative_meets_horizontal[OF pair rho s direction index entry face] by blast
 have weights: "v_degree (int rho) (-int s) P*int n=v_degree (int rho) (-int s) Q*int d \<and>
   v_degree 1 0 P*int n=v_degree 1 0 Q*int d"
   by (rule paired_face_points_common_weight_ratio[
     where P=P and Q=Q and a=a and b=b and n=n and d=d,
     OF aN aH bN bH x y])
 show ?thesis by (rule exI[where x=n], rule exI[where x=d])
   (intro conjI n d cop conjunct1[OF weights] conjunct2[OF weights])
qed
end
