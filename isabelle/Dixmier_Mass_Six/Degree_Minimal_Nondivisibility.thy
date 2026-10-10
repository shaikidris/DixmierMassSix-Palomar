theory Degree_Minimal_Nondivisibility
 imports "Degree_Minimal_Pair"
   "Proper_Power_Descent"
   "Fourier_Diagonal_Endpoints"
begin

lemma degree_minimal_support_nonempty:
 fixes F::"complex bivariate"
 assumes F: "F\<noteq>0"
 shows "biv_support F\<noteq>{}"
proof
 assume empty: "biv_support F={}"
 have "F=0"
   by (rule biv_eqI) (use empty in \<open>auto simp: biv_support_def\<close>)
 then show False using F by contradiction
qed

lemma counterexample_diagonal_weight_eq_total_degree:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "v_degree 1 1 P=int(total_degree P)"
proof -
 have dir: "is_direction 1 1" by (simp add: is_direction_def)
 have pos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair dir])
 have nonzero: "leading_form 1 1 P\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF pos])
 obtain e where e: "e\<in>biv_support(leading_form 1 1 P)" using degree_minimal_support_nonempty[OF nonzero] by blast
 have total: "fst e+snd e=total_degree P" by (rule diagonal_face_point_total_degree[OF e])
 have weight: "pair_weight 1 1 e=v_degree 1 1 P"
   using e by (simp add: leading_form_def weighted_component_support)
 show ?thesis using total weight by (simp add: pair_weight_def)
qed

lemma totalDeg_neg_A1:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "total_degree(-P)=total_degree P"
proof -
 have neg: "(-P)=(\<lambda>p. smult (-1::complex) (P p))" by (rule ext) simp
 have symbol: "pbw_symbol(-P)=smult [:-1:] (pbw_symbol P)"
   by (simp only: neg; rule weyl_symbol_smult[OF P])
 have support: "biv_support(pbw_symbol(-P))=biv_support(pbw_symbol P)"
   by (simp add: symbol biv_support_def biv_coeff_smult)
 show ?thesis by (simp only: total_degree_def support)
qed

lemma degreeMinimal_swap_neg:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "is_degree_minimal_counterexample_pair Q (-P)"
proof -
 have pair: "is_counterexample_pair P Q" and least:
   "\<And>R S. is_counterexample_pair R S \<Longrightarrow> gcd(total_degree P)(total_degree Q)\<le>gcd(total_degree R)(total_degree S)"
   using minimal unfolding is_degree_minimal_counterexample_pair_def by blast+
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have swapped: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 show ?thesis using swapped least unfolding is_degree_minimal_counterexample_pair_def
   by (simp only: totalDeg_neg_A1[OF P] gcd.commute[of "total_degree Q" "total_degree P"]; blast)
qed

lemma degreeMinimal_totalDeg_not_dvd:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<not>total_degree P dvd total_degree Q"
proof
 assume divides: "total_degree P dvd total_degree Q"
 have pair: "is_counterexample_pair P Q" and least_gcd:
   "\<And>R S. is_counterexample_pair R S \<Longrightarrow> gcd(total_degree P)(total_degree Q)\<le>gcd(total_degree R)(total_degree S)"
   using minimal unfolding is_degree_minimal_counterexample_pair_def by blast+
 have dir: "is_direction 1 1" by (simp add: is_direction_def)
 have Ppos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair dir])
 have Pweight: "v_degree 1 1 P=int(total_degree P)" by (rule counterexample_diagonal_weight_eq_total_degree[OF pair])
 have a: "0<total_degree P" using Ppos Pweight by simp
 let ?values="\<lambda>b::nat. \<exists>T::complex poly_operator. is_counterexample_pair P T \<and> b=total_degree T"
 have exists: "\<exists>b. ?values b" using pair by blast
 have attained: "?values(Least ?values)" by (rule LeastI_ex[OF exists])
 obtain T where pairT: "is_counterexample_pair P T" and degreeT: "Least ?values=total_degree T" using attained by blast
 have leastT: "total_degree T\<le>total_degree U" if "is_counterexample_pair P U" for U
 proof -
   have member: "?values(total_degree U)" using that by blast
   show ?thesis using Least_le[where P="?values", OF member] by (simp only: degreeT)
 qed
 have base: "gcd(total_degree P)(total_degree Q)=total_degree P" using divides by simp
 have lower: "total_degree P\<le>gcd(total_degree P)(total_degree T)"
   using least_gcd[OF pairT] by (simp only: base)
 have upper: "gcd(total_degree P)(total_degree T)\<le>total_degree P" by (rule gcd_le1_nat) (use a in auto)
 have geq: "gcd(total_degree P)(total_degree T)=total_degree P" using lower upper by arith
 have PT: "total_degree P dvd total_degree T" using gcd_dvd2[of "total_degree P" "total_degree T"] by (simp only: geq)
 have Tpos: "0<v_degree 1 1 T"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pairT] dir])
 have Tweight: "v_degree 1 1 T=int(total_degree T)"
   by (rule counterexample_diagonal_weight_eq_total_degree[OF isCounterexamplePair_swap_neg[OF pairT]])
 obtain m omega c where m: "0<m" and c: "c\<noteq>0" and mc: "int m=v_degree 1 1 P"
   and oc: "int omega=v_degree 1 1 T" and power:
   "(leading_form 1 1 T)^m=[:[:c:]:]*(leading_form 1 1 P)^omega"
   using counterexample_leading_faces_power_ratio[OF pairT dir] by blast
 have ma: "m=total_degree P" using mc Pweight by simp
 have ob: "omega=total_degree T" using oc Tweight by simp
 have exponent_divides: "m dvd omega" using PT by (simp only: ma ob)
 obtain nu k where nu: "nu\<noteq>0" and exponent: "omega=m*k"
   and face: "leading_form 1 1 T=[:[:nu:]:]*(leading_form 1 1 P)^k"
   using scalar_power_of_divisible_exponents[OF m c power exponent_divides] by blast
 have kp: "0<k" using exponent oc Tpos by (cases "k=0") auto
 obtain n where kn: "k=Suc n" using kp by (cases k) auto
 have weight: "v_degree 1 1 T=int(Suc n)*v_degree 1 1 P"
 proof -
   have "v_degree 1 1 T=int omega" by (rule oc[symmetric])
   also have "...=int m*int(Suc n)" by (simp only: exponent kn of_nat_mult)
   also have "...=int(Suc n)*v_degree 1 1 P" by (simp only: mc mult.commute)
   finally show ?thesis .
 qed
 have face_scalar: "leading_form 1 1 T=smult [:nu:] ((leading_form 1 1 P)^Suc n)"
   using face by (simp add: kn)
 let ?U="T-(\<lambda>p. smult nu ((P ^^ Suc n) p))"
 have pairU: "is_counterexample_pair P ?U" by (rule isCounterexamplePair_mateSubtraction[OF pairT])
 have P: "P\<in>weyl_algebra" and T: "T\<in>weyl_algebra" using pairT by (auto simp: is_counterexample_pair_def)
 have Pdegree: "weighted_degree 1 1 (pbw_symbol P)=bot.Value(v_degree 1 1 P)"
   by (rule weightedDegree_eq_coe_of_vDeg_pos[OF Ppos])
 have Tdegree: "weighted_degree 1 1 (pbw_symbol T)=bot.Value(int(Suc n)*v_degree 1 1 P)"
   using weightedDegree_eq_coe_of_vDeg_pos[OF Tpos] by (simp only: weight)
 have nextpositive: "0<int(Suc n)*v_degree 1 1 P" using Tpos by (simp only: weight)
 have drop: "v_degree 1 1 ?U<v_degree 1 1 T"
   using mateSubtraction_weight_drop_of_power_face[OF P T nu _ nextpositive Pdegree Tdegree face_scalar]
   by (simp only: weight; simp)
 have Uweight: "v_degree 1 1 ?U=int(total_degree ?U)"
   by (rule counterexample_diagonal_weight_eq_total_degree[OF isCounterexamplePair_swap_neg[OF pairU]])
 have decrease: "total_degree ?U<total_degree T" using drop by (simp only: Uweight Tweight; simp)
 show False using leastT[OF pairU] decrease by arith
qed

lemma degreeMinimal_totalDeg_nondivisibility:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<not>total_degree P dvd total_degree Q \<and> \<not>total_degree Q dvd total_degree P"
proof -
 have pair: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have left: "\<not>total_degree P dvd total_degree Q" by (rule degreeMinimal_totalDeg_not_dvd[OF minimal])
 have right: "\<not>total_degree Q dvd total_degree P"
   using degreeMinimal_totalDeg_not_dvd[OF degreeMinimal_swap_neg[OF minimal]] by (simp only: totalDeg_neg_A1[OF P]; blast)
 show ?thesis using left right by blast
qed
end
