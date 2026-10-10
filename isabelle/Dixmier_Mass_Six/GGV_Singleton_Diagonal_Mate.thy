theory GGV_Singleton_Diagonal_Mate
 imports "GGV_Linear_Shear_Minimality"
   "Poisson_Homogeneous_Endpoints"
begin

lemma counterexample_singleton_diagonal_mate:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes pair: "is_counterexample_pair P Q"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
   and a: "0<a" and b: "0<b"
 shows "\<exists>c d::nat. 0<c \<and> 0<d \<and> total_degree Q=c+d \<and>
   (c,d)\<in>biv_support(leading_form 1 1 Q) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 1 Q). e=(c,d)) \<and> a*d=b*c"
proof -
 let ?R="leading_form 1 1 P"
 let ?S="leading_form 1 1 Q"
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have Ppos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree 1 1 Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have Rnz: "?R\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Ppos])
 have Snz: "?S\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Qpos])
 have Rhom: "pair_weight 1 1 e=v_degree 1 1 P" if "e\<in>biv_support ?R" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have Shom: "pair_weight 1 1 e=v_degree 1 1 Q" if "e\<in>biv_support ?S" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have bracket: "biv_poisson ?S ?R=0"
   by (rule counterexample_leadingPoisson_zero_all_directions[OF pair direction])
 have weight_nonzero: "(1::int)\<noteq>0 \<or> (1::int)\<noteq>0" by simp
 obtain u v r t where u: "u\<in>biv_support ?S" and v: "v\<in>biv_support ?S"
   and r: "r\<in>biv_support ?R" and t: "t\<in>biv_support ?R"
   and maximum: "\<forall>e\<in>biv_support ?S. pair_weight 1 (-1) e\<le>pair_weight 1 (-1) u"
   and minimum: "\<forall>e\<in>biv_support ?S. pair_weight 1 (-1) v\<le>pair_weight 1 (-1) e"
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
 have sumu: "int(fst u)+int(snd u)=v_degree 1 1 Q"
   using Shom[OF u] by (simp add: pair_weight_def)
 have sumv: "int(fst v)+int(snd v)=v_degree 1 1 Q"
   using Shom[OF v] by (simp add: pair_weight_def)
 have difference: "int(fst u)-int(fst v)=int(snd v)-int(snd u)" using sumu sumv by arith
 have cancel: "(int a+int b)*(int(fst u)-int(fst v))=0"
 proof -
   have "(int a+int b)*(int(fst u)-int(fst v))=
     int a*(int(snd v)-int(snd u))+int b*(int(fst u)-int(fst v))"
     by (simp only: distrib_right difference)
   also have "...=0" by (simp only: right_diff_distrib zu zv; arith)
   finally show ?thesis .
 qed
 have sum_nonzero: "int a+int b\<noteq>0" using a by simp
 have xeq: "fst u=fst v" using cancel by (simp add: sum_nonzero)
 have yeq: "snd u=snd v" using sumu sumv xeq by simp
 have uv: "u=v" by (rule prod_eqI[OF xeq yeq])
 have singleton: "e=u" if e: "e\<in>biv_support ?S" for e
 proof (rule exponent_eq_of_weights_eq_of_perp_eq[OF weight_nonzero])
   show "pair_weight 1 1 e=pair_weight 1 1 u" by (simp only: Shom[OF e] Shom[OF u])
   show "pair_weight 1 (-1) e=pair_weight 1 (-1) u"
     using maximum minimum e uv by (intro antisym) blast+
 qed
 have positive_sum: "0<fst u+snd u"
 proof (rule ccontr)
   assume nonpositive: "\<not>0<fst u+snd u"
   have xzero: "fst u=0" and yzero: "snd u=0" using nonpositive by arith+
   have zero_degree: "v_degree 1 1 Q=0" using sumu by (simp add: xzero yzero)
   show False using Qpos zero_degree by arith
 qed
 have xpos: "0<fst u"
 proof (rule ccontr)
   assume "\<not>0<fst u" then have zero: "fst u=0" by arith
   have "snd u=0" using prop_u a zero by simp
   then show False using positive_sum zero by simp
 qed
 have ypos: "0<snd u"
 proof (rule ccontr)
   assume "\<not>0<snd u" then have zero: "snd u=0" by arith
   have "fst u=0" using prop_u b zero by simp
   then show False using positive_sum zero by simp
 qed
 have degree: "total_degree Q=fst u+snd u"
   using sumu counterexample_diagonal_weight_eq_total_degree[OF isCounterexamplePair_swap_neg[OF pair]] by simp
 have point: "(fst u,snd u)\<in>biv_support ?S" using u by (simp only: prod.collapse)
 have only: "\<forall>e\<in>biv_support ?S. e=(fst u,snd u)"
 proof (intro ballI)
   fix e assume member: "e\<in>biv_support ?S"
   have "e=u" by (rule singleton[OF member])
   then show "e=(fst u,snd u)" by (simp only: prod.collapse)
 qed
 show ?thesis
 proof (rule exI[of _ "fst u"], rule exI[of _ "snd u"], intro conjI)
   show "0<fst u" by (rule xpos)
   show "0<snd u" by (rule ypos)
   show "total_degree Q=fst u+snd u" by (rule degree)
   show "(fst u,snd u)\<in>biv_support ?S" by (rule point)
   show "\<forall>e\<in>biv_support ?S. e=(fst u,snd u)" by (rule only)
   show "a*snd u=b*fst u" by (rule prop_u)
 qed
qed

lemma preliminary_companion_singleton_diagonal_pair_subrectangular:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and diagonal: "total_degree P=a+b" and occupied: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
   and a: "0<a" and b: "0<b"
 shows "\<exists>c d::nat. 0<c \<and> 0<d \<and>
   is_subrectangular_at P a b \<and> is_subrectangular_at Q c d \<and> a*d=b*c"
proof -
 obtain c d where c: "0<c" and d: "0<d" and degree: "total_degree Q=c+d"
   and point: "(c,d)\<in>biv_support(leading_form 1 1 Q)"
   and only: "\<forall>e\<in>biv_support(leading_form 1 1 Q). e=(c,d)"
   and proportional: "a*d=b*c"
   using counterexample_singleton_diagonal_mate[OF pair unique a b] by blast
 have rectangleP: "is_subrectangular_at P a b"
   by (rule preliminary_companion_singleton_diagonal_subrectangular[OF source pair diagonal occupied unique a b])
 have rectangleQ: "is_subrectangular_at Q c d"
   by (rule preliminary_companion_singleton_diagonal_subrectangular[OF source
     isCounterexamplePair_swap_neg[OF pair] degree point _ c d]) (use only in blast)
 show ?thesis by (intro exI[of _ c] exI[of _ d]) (use c d rectangleP rectangleQ proportional in blast)
qed

end
