theory Positive_Singleton_Mate_Face
 imports "GGV_Singleton_Diagonal_Mate"
   "Positive_Proportional_Mate_Descent"
begin

lemma counterexample_positive_singleton_proportional_mate:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes pair: "is_counterexample_pair P Q"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
   and sigma: "1\<le>sigma" and b: "0<b"
 shows "\<exists>c d::nat. 0<d \<and> a*d=b*c \<and>
   biv_support(leading_form 1 (int sigma) Q)={(c,d)} \<and>
   v_degree 1 (int sigma) Q=int(c+sigma*d)"
proof -
 let ?R="leading_form 1 (int sigma) P"
 let ?S="leading_form 1 (int sigma) Q"
 have direction: "is_direction 1 (int sigma)" by (simp add: is_direction_def)
 have Ppos: "0<v_degree 1 (int sigma) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree 1 (int sigma) Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have Rnz: "?R\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Ppos])
 have Snz: "?S\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Qpos])
 have Rhom: "pair_weight 1 (int sigma) e=v_degree 1 (int sigma) P" if "e\<in>biv_support ?R" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have Shom: "pair_weight 1 (int sigma) e=v_degree 1 (int sigma) Q" if "e\<in>biv_support ?S" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have bracket: "biv_poisson ?S ?R=0"
   by (rule counterexample_leadingPoisson_zero_all_directions[OF pair direction])
 have weight_nonzero: "(1::int)\<noteq>0 \<or> int sigma\<noteq>0" by simp
 obtain u v r t where u: "u\<in>biv_support ?S" and v: "v\<in>biv_support ?S"
   and r: "r\<in>biv_support ?R" and t: "t\<in>biv_support ?R"
   and maximum: "\<forall>e\<in>biv_support ?S. pair_weight (int sigma) (-1) e\<le>pair_weight (int sigma) (-1) u"
   and minimum: "\<forall>e\<in>biv_support ?S. pair_weight (int sigma) (-1) v\<le>pair_weight (int sigma) (-1) e"
   and detu: "(of_nat(snd u)::complex)* of_nat(fst r)- of_nat(fst u)* of_nat(snd r)=0"
   and detv: "(of_nat(snd v)::complex)* of_nat(fst t)- of_nat(fst v)* of_nat(snd t)=0"
   using poisson_homogeneous_support_endpoints_collinear[OF weight_nonzero Shom Rhom Snz Rnz bracket] by blast
 have rpair: "r=(a,b)" by (rule unique[OF r])
 have tpair: "t=(a,b)" by (rule unique[OF t])
 have castu: "(of_nat (a*snd u)::complex)= of_nat(b*fst u)"
   using detu by (simp add: rpair mult.commute)
 have castv: "(of_nat (a*snd v)::complex)= of_nat(b*fst v)"
   using detv by (simp add: tpair mult.commute)
 have prop_u: "a*snd u=b*fst u" using castu by (simp only: of_nat_eq_iff)
 have prop_v: "a*snd v=b*fst v" using castv by (simp only: of_nat_eq_iff)
 have cast_zu: "int(a*snd u)=int(b*fst u)"
   by (rule arg_cong[where f=int, OF prop_u])
 have cast_zv: "int(a*snd v)=int(b*fst v)"
   by (rule arg_cong[where f=int, OF prop_v])
 have zu: "int a*int(snd u)=int b*int(fst u)"
   using cast_zu by (simp only: of_nat_mult)
 have zv: "int a*int(snd v)=int b*int(fst v)"
   using cast_zv by (simp only: of_nat_mult)
 have sumu: "int(fst u)+int sigma*int(snd u)=v_degree 1 (int sigma) Q"
   using Shom[OF u] by (simp add: pair_weight_def mult.commute)
 have sumv: "int(fst v)+int sigma*int(snd v)=v_degree 1 (int sigma) Q"
   using Shom[OF v] by (simp add: pair_weight_def mult.commute)
 have cancel: "(int a+int sigma*int b)*(int(snd u)-int(snd v))=0"
 proof -
   have "(int a+int sigma*int b)*(int(snd u)-int(snd v))=
     int b*((int(fst u)+int sigma*int(snd u))-(int(fst v)+int sigma*int(snd v)))+
     (int a*int(snd u)-int b*int(fst u))-(int a*int(snd v)-int b*int(fst v))"
     by (simp add: algebra_simps)
   also have "...=0" by (simp only: sumu sumv zu zv diff_self mult_zero_right add_0)
   finally show ?thesis .
 qed
 have sigma_positive: "0<int sigma" using sigma by simp
 have b_positive: "0<int b" using b by simp
 have product_positive: "0<int sigma*int b" by (rule mult_pos_pos[OF sigma_positive b_positive])
 have coefficient_nonzero: "int a+int sigma*int b\<noteq>0" using product_positive by arith
 have yeq: "snd u=snd v" using cancel by (simp add: coefficient_nonzero)
 have xeq: "fst u=fst v" using sumu sumv yeq by simp
 have uv: "u=v" by (rule prod_eqI[OF xeq yeq])
 have singleton: "e=u" if e: "e\<in>biv_support ?S" for e
 proof (rule exponent_eq_of_weights_eq_of_perp_eq[OF weight_nonzero])
   show "pair_weight 1 (int sigma) e=pair_weight 1 (int sigma) u" by (simp only: Shom[OF e] Shom[OF u])
   show "pair_weight (int sigma) (-1) e=pair_weight (int sigma) (-1) u"
     using maximum minimum e uv by (intro antisym) blast+
 qed
 have ypos: "0<snd u"
 proof (rule ccontr)
   assume "\<not>0<snd u" then have zero: "snd u=0" by arith
   have "fst u=0" using prop_u b zero by simp
   then show False using sumu Qpos zero by simp
 qed
 have support: "biv_support ?S={(fst u,snd u)}"
 proof (rule Set.set_eqI)
   fix e
   show "e\<in>biv_support ?S \<longleftrightarrow> e\<in>{(fst u,snd u)}"
   proof
     assume member: "e\<in>biv_support ?S"
     have equal: "e=u" by (rule singleton[OF member])
     show "e\<in>{(fst u,snd u)}" by (simp only: equal prod.collapse singleton_iff)
   next
     assume member: "e\<in>{(fst u,snd u)}"
     have equal: "e=u" using member by (simp only: prod.collapse singleton_iff)
     show "e\<in>biv_support ?S" by (simp only: equal u)
   qed
 qed
 have weight: "v_degree 1 (int sigma) Q=int(fst u+sigma*snd u)" using sumu by simp
 show ?thesis by (rule exI[of _ "fst u"], rule exI[of _ "snd u"])
   (use ypos prop_u support weight in blast)
qed

lemma counterexample_positive_singleton_finite_descent_pair:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes pair: "is_counterexample_pair P Q" and sigma: "1\<le>sigma" and b: "0<b"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
 shows "\<exists>c d R S. 0<d \<and> a*d=b*c \<and> v_degree 1 (int sigma) Q=int(c+sigma*d) \<and>
   is_counterexample_pair R S \<and> total_degree R=a+b \<and> total_degree S=c+d"
proof -
 obtain c d where d: "0<d" and proportional: "a*d=b*c"
   and support: "biv_support(leading_form 1 (int sigma) Q)={(c,d)}"
   and weight: "v_degree 1 (int sigma) Q=int(c+sigma*d)"
   using counterexample_positive_singleton_proportional_mate[OF pair unique sigma b] by blast
 have point: "(c,d)\<in>biv_support(leading_form 1 (int sigma) Q)" by (simp add: support)
 have only: "e=(c,d)" if "e\<in>biv_support(leading_form 1 (int sigma) Q)" for e
   using that by (simp add: support)
 have bound: "\<forall>e\<in>biv_support(pbw_symbol Q). snd e\<le>d"
   by (rule preliminary_positive_last_point_y_bound[OF preliminary_companion_from_actual_GGV_companion
     isCounterexamplePair_swap_neg[OF pair] sigma point _ d]) (use only in auto)
 have rawpoint: "(c,d)\<in>biv_support(pbw_symbol Q)" using point by (simp add: leading_form_def weighted_component_support)
 obtain R S where RS: "is_counterexample_pair R S" and Rdegree: "total_degree R=a+b" and Sdegree: "total_degree S=c+d"
   using preliminary_positive_proportional_finite_descent_both_degrees[OF preliminary_companion_from_actual_GGV_companion
     pair sigma b member unique _ rawpoint proportional] bound by blast
 show ?thesis using d proportional weight RS Rdegree Sdegree by blast
qed

end
