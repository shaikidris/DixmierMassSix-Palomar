theory Common_Root_Occupied_Endpoints
 imports "Homogeneous_Power_Endpoints"
   "Weyl_Statement_Interfaces"
begin

text \<open>Exact GGVCommonRootOccupiedEndpoints.lean source architecture,
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

lemma negative_homogeneous_x_le_of_y_le:
 fixes R::"complex bivariate" and rho s::nat and w::int
 assumes rho: "0<rho" and s: "0<s"
   and homogeneous: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) x=w"
   and e: "e\<in>biv_support R" and f: "f\<in>biv_support R"
   and y: "snd e\<le>snd f"
 shows "fst e\<le>fst f"
proof -
 have weights: "int rho*(int(fst e)-int(fst f))=
   int s*(int(snd e)-int(snd f))"
   using homogeneous[OF e] homogeneous[OF f] by (simp add: pair_weight_def algebra_simps)
 have nonpositive: "int s*(int(snd e)-int(snd f))\<le>0"
   using y by (intro mult_nonneg_nonpos) simp_all
 show ?thesis
 proof (rule ccontr)
   assume "\<not>fst e\<le>fst f"
   then have difference: "0<int(fst e)-int(fst f)" by simp
   have product: "0<int rho*(int(fst e)-int(fst f))"
     by (rule mult_pos_pos) (use rho in simp, rule difference)
   show False using product weights nonpositive by linarith
 qed
qed

lemma negative_face_power_inherits_occupied_endpoints:
 fixes P::"complex poly_operator" and R::"complex bivariate" and nu::complex
   and rho s m::nat and w::int
 assumes P: "P\<in>weyl_algebra" and rho: "0<rho" and s: "0<s"
   and R: "R\<noteq>0" and nu: "nu\<noteq>0"
   and homogeneous: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) x=w"
   and face: "leading_form (int rho) (-int s) P=smult [:nu:] (R^m)"
   and e: "e\<in>biv_support(leading_form (int rho) (-int s) P)"
   and f: "f\<in>biv_support(leading_form (int rho) (-int s) P)"
   and emin: "\<And>x. x\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd e\<le>snd x"
   and fmax: "\<And>x. x\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd x\<le>snd f"
 shows "\<exists>u v r t::nat. (u,v)\<in>biv_support R \<and> (r,t)\<in>biv_support R \<and>
 (\<forall>x\<in>biv_support R. fst x\<le>u) \<and> (\<forall>x\<in>biv_support R. r\<le>fst x) \<and>
 e=(m*r,m*t) \<and> f=(m*u,m*v)"
proof -
 let ?S="biv_support R"
 have nonempty: "?S\<noteq>{}" using R by simp
 have max_member: "Max(fst ` ?S)\<in>fst ` ?S" by (rule Max_in) (use nonempty in auto)
 have min_member: "Min(fst ` ?S)\<in>fst ` ?S" by (rule Min_in) (use nonempty in auto)
 obtain u v where endpt: "(u,v)\<in>?S" and endx: "u=Max(fst ` ?S)"
   using max_member by (auto simp: image_iff)
 obtain r t where start: "(r,t)\<in>?S" and startx: "r=Min(fst ` ?S)"
   using min_member by (auto simp: image_iff)
 have xmax: "fst x\<le>u" if "x\<in>?S" for x
   unfolding endx by (rule Max_ge) (simp, rule imageI[OF that])
 have xmin: "r\<le>fst x" if "x\<in>?S" for x
   unfolding startx by (rule Min_le) (simp, rule imageI[OF that])
 have ep: "(m*u,m*v)\<in>biv_support(leading_form (int rho) (-int s) P)"
   and sp: "(m*r,m*t)\<in>biv_support(leading_form (int rho) (-int s) P)"
   and maxp: "\<forall>x\<in>biv_support(leading_form (int rho) (-int s) P). fst x\<le>m*u"
   and minp: "\<forall>x\<in>biv_support(leading_form (int rho) (-int s) P). m*r\<le>fst x"
   using leadingFace_power_endpoint_pair[where rho=rho and s=s and m=m and u=u and v=v and r=r and t=t,
     OF P R nu s homogeneous endpt start xmax xmin face] by blast+
 have phom: "pair_weight (int rho) (-int s) x=v_degree (int rho) (-int s) P"
   if "x\<in>biv_support(leading_form (int rho) (-int s) P)" for x
   using that unfolding leading_form_def by (simp add: weighted_component_support)
 have ex: "fst e=m*r"
 proof (rule antisym)
   show "fst e\<le>m*r"
     using negative_homogeneous_x_le_of_y_le[OF rho s phom e sp emin[OF sp]] by simp
   show "m*r\<le>fst e" using minp e by blast
 qed
 have fx: "fst f=m*u"
 proof (rule antisym)
   show "fst f\<le>m*u" using maxp f by blast
   show "m*u\<le>fst f"
     using negative_homogeneous_x_le_of_y_le[OF rho s phom ep f fmax[OF ep]] by simp
 qed
 have eeq: "e=(m*r,m*t)" by (rule homogeneous_max_x_unique[OF s phom sp e ex])
 have feq: "f=(m*u,m*v)" by (rule homogeneous_max_x_unique[OF s phom ep f fx])
 show ?thesis using endpt start xmax xmin eeq feq by blast
qed

lemma leadingFace_root_endpoint_scaled_totalDeg_le:
 fixes P::"complex poly_operator" and R::"complex bivariate" and nu::complex
   and rho s m u v::nat and w::int
 assumes P: "P\<in>weyl_algebra" and R: "R\<noteq>0" and nu: "nu\<noteq>0" and s: "0<s"
   and homogeneous: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) x=w"
   and endpt: "(u,v)\<in>biv_support R"
   and xmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> fst x\<le>u"
   and face: "leading_form (int rho) (-int s) P=smult [:nu:] (R^m)"
 shows "m*(u+v)\<le>total_degree P"
proof -
 have occupied: "(m*u,m*v)\<in>biv_support(R^m)"
   by (rule homogeneous_power_max_x_endpoint[OF R s homogeneous endpt xmax])
 have occupied_face: "(m*u,m*v)\<in>biv_support(leading_form (int rho) (-int s) P)"
   using occupied nu by (auto simp: face biv_support_def biv_coeff_def)
 have raw: "(m*u,m*v)\<in>biv_support(pbw_symbol P)"
   using occupied_face by (simp add: leading_form_def weighted_component_support)
 have image_member: "(\<lambda>x. fst x+snd x) (m*u,m*v)\<in>
   (\<lambda>x. fst x+snd x) ` biv_support(pbw_symbol P)"
   by (rule imageI[OF raw])
 have bound: "m*u+m*v\<le>total_degree P"
   unfolding total_degree_def
 proof (rule Max_ge)
   show "finite(insert 0 ((\<lambda>x. fst x+snd x) ` biv_support(pbw_symbol P)))" by simp
   show "m*u+m*v\<in>insert 0 ((\<lambda>x. fst x+snd x) ` biv_support(pbw_symbol P))"
     by (rule insertI2) (use image_member in \<open>simp only: fst_conv snd_conv\<close>)
 qed
 show ?thesis using bound by (simp add: algebra_simps)
qed

lemma negative_face_root_crossing_and_gcd_bound:
 fixes P Q::"complex poly_operator" and R::"complex bivariate" and nu::complex
   and rho s m::nat and w::int
 assumes P: "P\<in>weyl_algebra" and rho: "0<rho" and s: "0<s" and m: "0<m"
   and R: "R\<noteq>0" and nu: "nu\<noteq>0"
   and homogeneous: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) x=w"
   and face: "leading_form (int rho) (-int s) P=smult [:nu:] (R^m)"
   and degree: "total_degree P=m*gcd(total_degree P)(total_degree Q)"
   and e: "e\<in>biv_support(leading_form (int rho) (-int s) P)"
   and f: "f\<in>biv_support(leading_form (int rho) (-int s) P)"
   and emin: "\<And>x. x\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd e\<le>snd x"
   and fmax: "\<And>x. x\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd x\<le>snd f"
   and positive: "0<pair_grade e" and negative: "pair_grade f<0"
 shows "\<exists>u v r t::nat. (u,v)\<in>biv_support R \<and> (r,t)\<in>biv_support R \<and>
 (\<forall>x\<in>biv_support R. fst x\<le>u) \<and> (\<forall>x\<in>biv_support R. r\<le>fst x) \<and>
 t<r \<and> u<v \<and> r<u \<and> u+v\<le>gcd(total_degree P)(total_degree Q) \<and>
 e=(m*r,m*t) \<and> f=(m*u,m*v)"
proof -
 obtain u v r t where endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
   and max: "\<forall>x\<in>biv_support R. fst x\<le>u" and min: "\<forall>x\<in>biv_support R. r\<le>fst x"
   and eeq: "e=(m*r,m*t)" and feq: "f=(m*u,m*v)"
   using negative_face_power_inherits_occupied_endpoints[OF P rho s R nu homogeneous face e f emin fmax] by blast
 have tr_product: "int(m*t)<int(m*r)" using positive by (simp add: eeq pair_grade_def)
 have tr_nat: "m*t<m*r" using tr_product by (simp only: of_nat_less_iff)
 have tr: "t<r" using tr_nat by (simp only: mult_less_cancel1; blast)
 have uv_product: "int(m*u)<int(m*v)" using negative by (simp add: feq pair_grade_def)
 have uv_nat: "m*u<m*v" using uv_product by (simp only: of_nat_less_iff)
 have uv: "u<v" using uv_nat by (simp only: mult_less_cancel1; blast)
 have ru: "r\<le>u" using max start by auto
 have different: "r\<noteq>u"
 proof
   assume equal: "r=u"
   have endpoint_x: "fst(r,t)=u" by (simp only: fst_conv; rule equal)
   have same: "(r,t)=(u,v)"
     by (rule homogeneous_max_x_unique[OF s homogeneous endpt start endpoint_x])
   show False using same tr uv by auto
 qed
 have strict: "r<u" using ru different by arith
 have xmax: "fst x\<le>u" if "x\<in>biv_support R" for x
   by (rule bspec[OF max that])
 have scaled: "m*(u+v)\<le>total_degree P"
   by (rule leadingFace_root_endpoint_scaled_totalDeg_le[OF P R nu s homogeneous endpt xmax face])
 have scaled_gcd: "m*(u+v)\<le>m*gcd(total_degree P)(total_degree Q)"
 proof -
   have "m*(u+v)\<le>total_degree P" by (rule scaled)
   also have "...=m*gcd(total_degree P)(total_degree Q)" by (rule degree)
   finally show ?thesis .
 qed
 have bound: "u+v\<le>gcd(total_degree P)(total_degree Q)"
   using scaled_gcd m by (simp only: mult_le_cancel1; blast)
 show ?thesis using endpt start max min tr uv strict bound eeq feq by blast
qed

end
