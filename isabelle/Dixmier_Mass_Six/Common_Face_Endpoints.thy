theory Common_Face_Endpoints
 imports "Global_Face_Power_Ratio"
   "Homogeneous_Power_Endpoints"
begin

lemma counterexample_reduced_face_weight_ratio:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "\<exists>n d::nat. 0<n \<and> 0<d \<and> coprime d n \<and>
   nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
proof -
 let ?m="nat(v_degree rho sigma P)" let ?w="nat(v_degree rho sigma Q)"
 let ?g="gcd ?m ?w" let ?d="?m div ?g" let ?n="?w div ?g"
 have m: "0<?m" using counterexample_vDeg_pos_all_directions[OF pair direction] by simp
 have w: "0<?w" using counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction] by simp
 have g: "0<?g" using m by simp
 have ma: "?g*?d=?m" by (simp add: dvd_mult_div_cancel gcd_dvd1)
 have wn: "?g*?n=?w" by (simp add: dvd_mult_div_cancel gcd_dvd2)
 have d: "0<?d" using ma m by (cases "?d=0") auto
 have n: "0<?n" using wn w by (cases "?n=0") auto
 have primitive: "coprime ?d ?n" by (rule div_gcd_coprime) (use m in auto)
 have products: "?g*(?w*?d)=?g*(?m*?n)"
 proof -
   have "?g*(?w*?d)=?w*(?g*?d)" by (simp only: mult.assoc mult.commute mult.left_commute)
   also have "...=?w*?m" by (simp only: ma)
   also have "...=?m*(?g*?n)" by (simp only: wn; simp only: mult.commute)
   also have "...=?g*(?m*?n)" by (simp only: mult.assoc mult.commute mult.left_commute)
   finally show ?thesis .
 qed
 have gn: "?g\<noteq>0" using g by arith
 have ratio: "?w*?d=?m*?n" using products by (simp only: mult_left_cancel[OF gn])
 show ?thesis by (intro exI[of _ ?n] exI[of _ ?d]) (use n d primitive ratio in blast)
qed

lemma counterexample_common_face_proportional_endpoints:
 fixes P Q::"complex poly_operator" and rho s n d::nat
 assumes pair: "is_counterexample_pair P Q" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)" and n: "0<n" and d: "0<d"
   and primitive: "coprime d n"
   and ratio: "nat(v_degree (int rho) (-int s) Q)*d=nat(v_degree (int rho) (-int s) P)*n"
 shows "\<exists>u v r t::nat.
 (d*u,d*v)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (n*u,n*v)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (d*r,d*t)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (n*r,n*t)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). d*r\<le>fst e \<and> fst e\<le>d*u) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) Q). n*r\<le>fst e \<and> fst e\<le>n*u)"
proof -
 obtain S nu mu degree where S: "S\<noteq>0" and nu: "nu\<noteq>0" and mu: "mu\<noteq>0"
   and hom: "weighted_homogeneous (int rho) (-int s) degree S"
   and Pshape: "leading_form (int rho) (-int s) P=[:[:nu:]:]*S^d"
   and Qshape: "leading_form (int rho) (-int s) Q=[:[:mu:]:]*S^n"
   using counterexample_leading_faces_homogeneous_common_root[OF pair direction n d primitive ratio] by blast
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" using pair by (auto simp: is_counterexample_pair_def)
 have homogeneous: "pair_weight (int rho) (-int s) e=degree" if "e\<in>biv_support S" for e
   using hom that by (simp add: weighted_homogeneous_def)
 have nonempty: "biv_support S\<noteq>{}" using S by simp
 have max_member: "Max(fst ` biv_support S)\<in>fst ` biv_support S" by (rule Max_in) (use nonempty in auto)
 have min_member: "Min(fst ` biv_support S)\<in>fst ` biv_support S" by (rule Min_in) (use nonempty in auto)
 obtain u v where endpt: "(u,v)\<in>biv_support S" and ux: "u=Max(fst ` biv_support S)" using max_member by (auto simp: image_iff)
 obtain r t where start: "(r,t)\<in>biv_support S" and rx: "r=Min(fst ` biv_support S)" using min_member by (auto simp: image_iff)
 have maximum: "fst e\<le>u" if "e\<in>biv_support S" for e unfolding ux by (rule Max_ge) (simp, rule imageI[OF that])
 have minimum: "r\<le>fst e" if "e\<in>biv_support S" for e unfolding rx by (rule Min_le) (simp, rule imageI[OF that])
 have Pface: "leading_form (int rho) (-int s) P=smult [:nu:] (S^d)" using Pshape by simp
 have Qface: "leading_form (int rho) (-int s) Q=smult [:mu:] (S^n)" using Qshape by simp
 have Pd: "(d*u,d*v)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (d*r,d*t)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). fst e\<le>d*u) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). d*r\<le>fst e)"
   by (rule leadingFace_power_endpoint_pair[OF P S nu s homogeneous endpt start maximum minimum Pface])
 have Qd: "(n*u,n*v)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (n*r,n*t)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) Q). fst e\<le>n*u) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) Q). n*r\<le>fst e)"
   by (rule leadingFace_power_endpoint_pair[OF Q S mu s homogeneous endpt start maximum minimum Qface])
 show ?thesis by (intro exI[of _ u] exI[of _ v] exI[of _ r] exI[of _ t]) (use Pd Qd in blast)
qed

lemma counterexample_strict_negative_face_proportional_endpoints:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes pair: "is_counterexample_pair P Q" and s: "0<s" and direction: "is_direction (int rho) (-int s)"
 shows "\<exists>n d u v r t::nat. 0<n \<and> 0<d \<and> coprime d n \<and>
 (d*u,d*v)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (n*u,n*v)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (d*r,d*t)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (n*r,n*t)\<in>biv_support(leading_form (int rho) (-int s) Q) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). d*r\<le>fst e \<and> fst e\<le>d*u) \<and>
 (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) Q). n*r\<le>fst e \<and> fst e\<le>n*u)"
proof -
 obtain n d where n: "0<n" and d: "0<d" and primitive: "coprime d n"
   and ratio: "nat(v_degree (int rho) (-int s) Q)*d=nat(v_degree (int rho) (-int s) P)*n"
   using counterexample_reduced_face_weight_ratio[OF pair direction] by blast
 show ?thesis using n d primitive counterexample_common_face_proportional_endpoints[OF pair s direction n d primitive ratio] by blast
qed
end
