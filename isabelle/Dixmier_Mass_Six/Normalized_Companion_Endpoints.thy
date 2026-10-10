theory Normalized_Companion_Endpoints
 imports "GGV_Case_Field_Adapter"
   "Primitive_Direction_Arithmetic"
   "Small_Degree_Coordinate_Adapter"
   "Companion_Nonmonomial"
   "Homogeneous_Endpoint_Arithmetic"
begin

lemma companion_support_recovers_primitive_direction:
 fixes F::"complex bivariate" and rho s f1 f2::nat and degree::int
 assumes direction: "is_direction(int rho)(-int s)" and f1: "2\<le>f1"
   and homogeneous: "weighted_homogeneous(int rho)(-int s) degree F"
   and base: "(1,1)\<in>biv_support F" and endpt: "(f1,f2)\<in>biv_support F"
 shows "rho=(f2-1) div gcd(f1-1)(f2-1) \<and> s=(f1-1) div gcd(f1-1)(f2-1)"
proof -
 have rho: "0<rho" using direction by (simp add: is_direction_def; arith)
 have primitive: "coprime rho s" using direction by (simp add: is_direction_def coprime_iff_gcd_eq_1)
 have bw: "pair_weight(int rho)(-int s)(1,1)=degree" and ew: "pair_weight(int rho)(-int s)(f1,f2)=degree"
   using homogeneous base endpt unfolding weighted_homogeneous_def by blast+
 have weights: "int rho*int f1-int s*int f2=int rho-int s"
   using bw ew by (simp add: pair_weight_def mult.commute)
 have f2: "1\<le>f2"
 proof (rule ccontr)
   assume "\<not>1\<le>f2"
   then have zero: "f2=0" by arith
   have product: "0<int rho*(int f1-1)" using rho f1 by (intro mult_pos_pos) simp_all
   show False using weights product by (simp add: zero algebra_simps; linarith)
 qed
 have signed: "int(rho*(f1-1))=int(s*(f2-1))"
   using weights f1 f2 by (simp add: of_nat_diff algebra_simps; linarith)
 have line: "rho*(f1-1)=s*(f2-1)" using signed by (simp only: of_nat_eq_iff)
 have first_positive: "0<f1-1" using f1 by arith
 show ?thesis by (rule primitive_direction_of_weight_line[OF rho first_positive primitive line])
qed

lemma homogeneous_small_degree_forbidden_corner:
 fixes R F::"complex bivariate" and rho s u v r t f1 f2::nat and degree degreeF::int
 assumes Rhom: "weighted_homogeneous(int rho)(-int s) degree R"
   and Fhom: "weighted_homogeneous(int rho)(-int s) degreeF F"
   and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
   and base: "(1,1)\<in>biv_support F" and Fend: "(f1,f2)\<in>biv_support F"
   and crossing: "u<v" and small: "u+v\<le>15" and f1: "2\<le>f1" and proportional: "f1*v=f2*u"
   and start_positive: "t<r" and predecessor: "r<u" and direction: "is_direction(int rho)(-int s)"
 shows "let d=gcd(f1-1)(f2-1); rho'=(f2-1) div d; s'=(f1-1) div d in
 d=1 \<and> 0<rho' \<and> (\<exists>h::nat. 2\<le>h \<and> t\<le>h \<and> v=t+rho'*h \<and> rho'*r+(h-t)*s'=rho'*h-1)"
proof -
 have normalized: "rho=(f2-1) div gcd(f1-1)(f2-1) \<and> s=(f1-1) div gcd(f1-1)(f2-1)"
   by (rule companion_support_recovers_primitive_direction[OF direction f1 Fhom base Fend])
 have homogeneous: "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight(int rho)(-int s) e=degree"
   using Rhom unfolding weighted_homogeneous_def by blast
 have line: "rho*u+s*t=rho*r+s*v" by (rule homogeneous_endpoints_weight_equation[OF homogeneous endpt start])
 have normalized_line: "let d=gcd(f1-1)(f2-1); rho'=(f2-1) div d; s'=(f1-1) div d in
   rho'*u+s'*t=rho'*r+s'*v" using normalized line by simp
 show ?thesis by (rule ggv_small_degree_coordinates_forbidden_corner[OF crossing small f1 proportional start_positive predecessor normalized_line])
qed

lemma counterexample_crossing_root_companion_endpoint:
 fixes P Q::"complex poly_operator" and R::"complex bivariate" and nu::complex
   and rho s m u v r t::nat and w::int
 assumes pair: "is_counterexample_pair P Q" and s: "0<s" and m: "0<m"
   and direction: "is_direction(int rho)(-int s)" and R: "R\<noteq>0" and nu: "nu\<noteq>0"
   and homogeneous: "weighted_homogeneous(int rho)(-int s) w R"
   and face: "leading_form(int rho)(-int s) P=[:[:nu:]:]*R^m"
   and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
   and max: "\<And>e. e\<in>biv_support R \<Longrightarrow> fst e\<le>u"
   and start_positive: "t<r" and end_negative: "u<v"
 shows "\<exists>F::complex bivariate. \<exists>f1 f2::nat.
 weighted_homogeneous(int rho)(-int s)(int rho-int s) F \<and>
 biv_poisson R F=R \<and> (1,1)\<in>biv_support F \<and> 1<card(biv_support F) \<and>
 (f1,f2)\<in>biv_support F \<and> (\<forall>e\<in>biv_support F. fst e\<le>f1) \<and>
 2\<le>f1 \<and> f1*v=f2*u \<and>
 rho=(f2-1) div gcd(f1-1)(f2-1) \<and> s=(f1-1) div gcd(f1-1)(f2-1)"
proof -
 have source: "GGVPreliminaryCompanionInput" by (rule preliminary_companion_from_actual_GGV_companion)
 have all_pairs: "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
   (\<forall>rho sigma. is_direction rho sigma \<longrightarrow>
    (\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and>
      biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P))"
   using source unfolding GGVPreliminaryCompanionInput_def .
 have available: "is_counterexample_pair P Q \<longrightarrow>
   (\<forall>rho sigma. is_direction rho sigma \<longrightarrow>
    (\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and>
      biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P))"
   by (rule spec[OF spec[OF all_pairs, of P], of Q])
 have directions: "\<forall>rho sigma. is_direction rho sigma \<longrightarrow>
    (\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and>
      biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P)"
   by (rule mp[OF available pair])
 have at_direction: "\<exists>F. weighted_homogeneous (int rho) (-int s) (int rho-int s) F \<and>
    biv_poisson (leading_form (int rho) (-int s) P) F=leading_form (int rho) (-int s) P"
   using mp[OF spec[OF spec[OF directions, of "int rho"], of "-int s"] direction]
   by (simp only: diff_conv_add_uminus)
 obtain F0 where F0hom: "weighted_homogeneous(int rho)(-int s)(int rho-int s) F0"
   and F0br: "biv_poisson ([:[:nu:]:]*R^m) F0=[:[:nu:]:]*R^m"
   using at_direction by (simp only: face; blast)
 let ?F="[:[:of_nat m:]:]*F0"
 have Fhom: "weighted_homogeneous(int rho)(-int s)(int rho-int s) ?F"
   by (rule native_homogeneous_scalar_multiple[OF F0hom])
 have companion: "biv_poisson R ?F=R" by (rule poisson_power_companion_cancel[OF nu m R F0br])
 have slope: "s<rho" using direction by (simp add: is_direction_def; arith)
 have Fpointwise: "\<And>e. e\<in>biv_support ?F \<Longrightarrow> pair_weight(int rho)(-int s) e=int rho-int s"
   using Fhom unfolding weighted_homogeneous_def by blast
 have Rpointwise: "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight(int rho)(-int s) e=w"
   using homogeneous unfolding weighted_homogeneous_def by blast
 have base: "(1,1)\<in>biv_support ?F" by (rule homogeneous_companion_base_mem[OF s slope R Fpointwise companion])
 have positive: "0<pair_grade(r,t)" and negative: "pair_grade(u,v)<0"
   using start_positive end_negative by (simp_all add: pair_grade_def)
 have nonmonomial: "1<card(biv_support ?F)"
   by (rule crossing_poisson_companion_nonmonomial[OF base companion start endpt positive negative])
 have nonempty: "biv_support ?F\<noteq>{}" using base by blast
 have attained: "Max(fst ` biv_support ?F)\<in>fst ` biv_support ?F" by (rule Max_in) (use nonempty in auto)
 obtain f1 f2 where Fend: "(f1,f2)\<in>biv_support ?F" and xmax: "f1=Max(fst ` biv_support ?F)"
   using attained by (auto simp: image_iff)
 have Fmax: "fst e\<le>f1" if "e\<in>biv_support ?F" for e unfolding xmax by (rule Max_ge) (simp, rule imageI[OF that])
 have first: "2\<le>f1" by (rule homogeneous_companion_end_x_ge_two[OF s direction Fpointwise base Fmax nonmonomial])
 have endpoint_proportional: "f1*v=f2*u" by (rule homogeneous_companion_end_proportional[OF s first Rpointwise Fpointwise endpt Fend max Fmax companion])
 have normalized: "rho=(f2-1) div gcd(f1-1)(f2-1) \<and> s=(f1-1) div gcd(f1-1)(f2-1)"
   by (rule companion_support_recovers_primitive_direction[OF direction first Fhom base Fend])
 show ?thesis using Fhom companion base nonmonomial Fend Fmax first endpoint_proportional normalized by blast
qed

lemma counterexample_crossing_root_small_degree_coordinates:
 fixes P Q::"complex poly_operator" and R::"complex bivariate" and nu::complex
   and rho s m u v r t::nat and w::int
 assumes pair: "is_counterexample_pair P Q" and s: "0<s" and m: "0<m"
   and direction: "is_direction(int rho)(-int s)" and R: "R\<noteq>0" and nu: "nu\<noteq>0"
   and homogeneous: "weighted_homogeneous(int rho)(-int s) w R"
   and face: "leading_form(int rho)(-int s) P=[:[:nu:]:]*R^m"
   and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
   and max: "\<And>e. e\<in>biv_support R \<Longrightarrow> fst e\<le>u"
   and start_positive: "t<r" and end_negative: "u<v" and predecessor: "r<u" and small: "u+v\<le>15"
 shows "\<exists>F::complex bivariate. \<exists>f1 f2 h::nat.
 weighted_homogeneous(int rho)(-int s)(int rho-int s) F \<and>
 biv_poisson R F=R \<and> (1,1)\<in>biv_support F \<and>
 (f1,f2)\<in>biv_support F \<and> (\<forall>e\<in>biv_support F. fst e\<le>f1) \<and>
 2\<le>f1 \<and> f1*v=f2*u \<and> gcd(f1-1)(f2-1)=1 \<and>
 2\<le>h \<and> t\<le>h \<and> v=t+rho*h \<and> rho*r+(h-t)*s=rho*h-1"
proof -
 obtain F f1 f2 where Fhom: "weighted_homogeneous(int rho)(-int s)(int rho-int s) F"
   and companion: "biv_poisson R F=R" and base: "(1,1)\<in>biv_support F"
   and Fend: "(f1,f2)\<in>biv_support F" and Fmax: "\<forall>e\<in>biv_support F. fst e\<le>f1"
   and first: "2\<le>f1" and endpoint_proportional: "f1*v=f2*u"
   and normalized: "rho=(f2-1) div gcd(f1-1)(f2-1) \<and> s=(f1-1) div gcd(f1-1)(f2-1)"
   using counterexample_crossing_root_companion_endpoint[OF pair s m direction R nu homogeneous face endpt start max start_positive end_negative] by blast
 have corner: "gcd(f1-1)(f2-1)=1 \<and> (\<exists>h::nat. 2\<le>h \<and> t\<le>h \<and> v=t+rho*h \<and> rho*r+(h-t)*s=rho*h-1)"
   using homogeneous_small_degree_forbidden_corner[OF homogeneous Fhom endpt start base Fend end_negative small first endpoint_proportional start_positive predecessor direction]
   by (simp only: Let_def normalized[THEN conjunct1, symmetric] normalized[THEN conjunct2, symmetric]; blast)
 have gcd_one: "gcd(f1-1)(f2-1)=1" by (rule conjunct1[OF corner])
 obtain h where h: "2\<le>h" "t\<le>h" "v=t+rho*h" "rho*r+(h-t)*s=rho*h-1"
   using conjunct2[OF corner] by blast
 show ?thesis
   by (rule exI[where x=F], rule exI[where x=f1], rule exI[where x=f2], rule exI[where x=h])
      (intro conjI Fhom companion base Fend Fmax first endpoint_proportional gcd_one h)
qed
end
