theory Crossing_Mate_Descent_Terminal
 imports "Crossing_Face_Mate_Power"
  "Mate_Descent"
  "Leading_Powers"
  "GGV_Inputs"
begin

lemma vDeg_pos_of_positive_grade:
 fixes T::"complex poly_operator" and rho s::nat
 assumes T: "T\<in>weyl_algebra" and sr: "s<rho"
 and grade: "\<exists>e\<in>biv_support(pbw_symbol T). 0<pair_grade e"
 shows "0<v_degree (int rho) (-int s) T"
proof -
 obtain e where e: "e\<in>biv_support(pbw_symbol T)" and g: "0<pair_grade e" using grade by blast
 have rho: "0<int rho" using sr by (simp; arith)
 have sum: "0<int rho+(-int s)" using sr by simp
 have lower: "int rho\<le>pair_weight (int rho) (-int s) e"
   by (rule positive_grade_weight_ge_rho[OF rho sum g])
 show ?thesis using lower symbol_weight_le_v_degree[OF e, of "int rho" "-int s"] rho by arith
qed

lemma counterexample_mate_weight_pos:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes H: "GGVInputs" and pair: "is_counterexample_pair P Q" and sr: "s<rho"
 shows "0<v_degree (int rho) (-int s) Q"
proof -
 have swap: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have Q: "Q\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have grades: "GGVGradesInput" by (rule GGVInputs_grades_opposite[OF H])
 have grade: "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
   using grades swap unfolding GGVGradesInput_def by blast
 show ?thesis by (rule vDeg_pos_of_positive_grade[OF Q sr grade])
qed

lemma weightedDegree_eq_coe_of_vDeg_pos:
 fixes T::"complex poly_operator"
 assumes T: "T\<in>weyl_algebra" and positive: "0<v_degree rho sigma T"
 shows "weighted_degree rho sigma (pbw_symbol T)=bot.Value(v_degree rho sigma T)"
 using positive by (cases "weighted_degree rho sigma (pbw_symbol T)"; simp_all add: v_degree_def)

lemma crossing_scalar_power:
 "([:[:mu:]:]::complex bivariate)^n=[:[:mu^n:]:]"
 by (induction n; simp_all add: one_pCons)

text \<open>Least positive mate weight is the native well-order presentation
of the source strong-induction descent. The subtraction and strict drop
are the checked source producers; all intermediate mates remain unrestricted.\<close>

lemma crossingFace_mate_descent_terminal:
 fixes P Q::"complex poly_operator" and p q rho s::nat
 assumes H: "GGVInputs" and mu: "mu\<noteq>0" and p: "2\<le>p" and s: "0<s" and sr: "s<rho"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and pair: "is_counterexample_pair P Q"
 shows "\<exists>Q'::complex poly_operator. \<exists>j::nat. \<exists>nu::complex.
 is_counterexample_pair P Q' \<and> 0<j \<and> \<not>p dvd j \<and> nu\<noteq>0 \<and>
 v_degree (int rho) (-int s) Q'=int(rho*j) \<and>
 leading_form (int rho) (-int s) Q'=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
proof -
 let ?v="\<lambda>T::complex poly_operator. v_degree (int rho) (-int s) T"
 let ?property="\<lambda>N::nat. \<exists>T::complex poly_operator. is_counterexample_pair P T \<and> nat(?v T)=N"
 let ?N="Least ?property"
 have exists: "\<exists>N. ?property N" using pair by blast
 have chosen: "?property ?N" by (rule LeastI_ex[OF exists])
 obtain T where Tpair: "is_counterexample_pair P T" and measure: "nat(?v T)=?N"
   using chosen by blast
 have minimal: "?N\<le>nat(?v U)" if U: "is_counterexample_pair P U" for U
   by (rule Least_le) (use U in blast)
 have P: "P\<in>weyl_algebra" and T: "T\<in>weyl_algebra" and exact: "op_comp T P- op_comp P T=id"
   using Tpair by (auto simp: is_counterexample_pair_def)
 have Tpos: "0<?v T" by (rule counterexample_mate_weight_pos[OF H Tpair sr])
 have Tweight: "?v T=int ?N" using Tpos measure by simp
 have Npos: "0<?N" using measure Tpos by simp
 obtain j nu where j: "0<j" and nu: "nu\<noteq>0" and Nj: "?N=rho*j"
 and Tf: "leading_form (int rho) (-int s) T=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
   using crossingFace_mate_is_base_power[OF P T mu p s sr Npos exact Pw Tweight Pf] by blast
 have not_divides: "\<not>p dvd j"
 proof
   assume divides: "p dvd j"
   obtain k where jk: "j=p*k" using divides by (elim dvdE)
   have kpos: "0<k" using j jk by (cases k) auto
   obtain a where k: "k=Suc a" using kpos by (cases k) auto
   let ?c="nu/(mu^Suc a)"
   let ?T'="T-(\<lambda>f. smult ?c ((P ^^ Suc a) f))"
   have c: "?c\<noteq>0" using nu mu by simp
   have mate_after: "is_counterexample_pair P ?T'" by (rule isCounterexamplePair_mateSubtraction[OF Tpair])
   have nextpos: "0<?v ?T'" by (rule counterexample_mate_weight_pos[OF H mate_after sr])
   have rho: "0<int rho" using sr by (simp; arith)
   have sum: "0<int rho+(-int s)" using sr by simp
   have ppos: "0<int p" using p by (simp; arith)
   have Ppos: "0<?v P" using rho ppos by (simp only: Pw; simp)
   have Pdegree: "weighted_degree (int rho) (-int s) (pbw_symbol P)=bot.Value(int p*int rho)"
     using weightedDegree_eq_coe_of_vDeg_pos[OF P Ppos] by (simp only: Pw)
   have weight: "?v T=int(Suc a)*(int p*int rho)"
     by (simp only: Tweight Nj jk k; simp add: algebra_simps)
   have positive: "0<int(Suc a)*(int p*int rho)" using Tpos by (simp only: weight)
   have Tdegree: "weighted_degree (int rho) (-int s) (pbw_symbol T)=bot.Value(int(Suc a)*(int p*int rho))"
     using weightedDegree_eq_coe_of_vDeg_pos[OF T Tpos] by (simp only: weight)
   have face: "leading_form (int rho) (-int s) T=
     smult [:?c:] ((leading_form (int rho) (-int s) P)^Suc a)"
   proof -
     have power: "((leading_form (int rho) (-int s) P)^Suc a)=
       [:[:mu^Suc a:]:]*(crossing_primitive_base alpha q rho s)^j"
       by (simp only: Pf power_mult_distrib crossing_scalar_power power_mult[symmetric] jk k)
     show ?thesis by (simp only: power Tf; simp add: mu)
   qed
   have drop: "?v ?T'<int(Suc a)*(int p*int rho)"
     by (rule mateSubtraction_weight_drop_of_power_face[OF P T c sum positive Pdegree Tdegree face])
   have strict: "?v ?T'<int ?N" using drop by (simp only: weight[symmetric] Tweight)
   have decrease: "nat(?v ?T')<?N" using strict nextpos Npos by simp
   show False using minimal[OF mate_after] decrease by arith
 qed
 have finalweight: "?v T=int(rho*j)" by (simp only: Tweight Nj)
 show ?thesis
   by (rule exI[where x=T], rule exI[where x=j], rule exI[where x=nu], intro conjI)
      (rule Tpair j not_divides nu finalweight Tf)+
qed

end
