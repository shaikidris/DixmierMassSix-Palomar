theory Horizontal_Mate_Descent
 imports "Horizontal_Mate_Power"
begin

lemma horizontal_counterexample_mate_weight_pos:
 fixes P Q::"complex poly_operator"
 assumes H: "GGVInputs" and pair: "is_counterexample_pair P Q"
 shows "0<v_degree 1 0 Q"
 using counterexample_mate_weight_pos[where rho=1 and s=0, OF H pair]
 by simp

lemma horizontal_mate_descent_terminal:
 fixes P Q::"complex poly_operator" and p::nat
 assumes H: "GGVInputs" and mu: "mu\<noteq>0" and p: "2\<le>p"
 and Pw: "v_degree 1 0 P=int p"
 and Pf: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
 and pair: "is_counterexample_pair P Q"
 shows "\<exists>Q'::complex poly_operator. \<exists>j::nat. \<exists>nu::complex.
 is_counterexample_pair P Q' \<and>0<j \<and>\<not>p dvd j \<and>nu\<noteq>0 \<and>
 v_degree 1 0 Q'=int j \<and>
 leading_form 1 0 Q'=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
proof -
 let ?v="\<lambda>T::complex poly_operator. v_degree (1) 0 T"
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
 have Tpos: "0<?v T" by (rule horizontal_counterexample_mate_weight_pos[OF H Tpair])
 have Tweight: "?v T=int ?N" using Tpos measure by simp
 have Npos: "0<?N" using measure Tpos by simp
 obtain j nu where j: "0<j" and nu: "nu\<noteq>0"
 and jw: "?v T=int j"
 and Tf: "leading_form 1 0 T=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
   using horizontal_mate_is_base_power[OF H mu p Pf Tpair] by blast
 have Nj: "?N=j" using Tweight jw by simp
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
   have nextpos: "0<?v ?T'" by (rule horizontal_counterexample_mate_weight_pos[OF H mate_after])
   have rho: "(0::int)<1" by simp
   have sum: "(0::int)<1+0" by simp
   have ppos: "0<int p" using p by (simp; arith)
   have Ppos: "0<?v P" using rho ppos by (simp add: Pw)
   have Pdegree: "weighted_degree (1) 0 (pbw_symbol P)=bot.Value(int p*1)"
     using weightedDegree_eq_coe_of_vDeg_pos[OF P Ppos] by (simp add: Pw)
   have weight: "?v T=int(Suc a)*(int p*1)"
     by (simp only: Tweight Nj jk k; simp add: algebra_simps)
   have positive: "0<int(Suc a)*(int p*1)" using Tpos by (simp only: weight)
   have Tdegree: "weighted_degree (1) 0 (pbw_symbol T)=bot.Value(int(Suc a)*(int p*1))"
     using weightedDegree_eq_coe_of_vDeg_pos[OF T Tpos] by (simp only: weight)
   have face: "leading_form (1) 0 T=
     smult [:?c:] ((leading_form (1) 0 P)^Suc a)"
   proof -
     have power: "((leading_form (1) 0 P)^Suc a)=
       [:[:mu^Suc a:]:]*(crossing_primitive_base alpha 2 1 0)^j"
       by (simp only: Pf power_mult_distrib crossing_scalar_power power_mult[symmetric] jk k)
     show ?thesis by (simp only: power Tf; simp add: mu)
   qed
   have drop: "?v ?T'<int(Suc a)*(int p*1)"
     by (rule mateSubtraction_weight_drop_of_power_face[OF P T c sum positive Pdegree Tdegree face])
   have strict: "?v ?T'<int ?N" using drop by (simp only: weight[symmetric] Tweight)
   have decrease: "nat(?v ?T')<?N" using strict nextpos Npos by simp
   show False using minimal[OF mate_after] decrease by arith
 qed
 have finalweight: "?v T=int(j)" by (simp only: Tweight Nj)
 show ?thesis
   by (rule exI[where x=T], rule exI[where x=j], rule exI[where x=nu], intro conjI)
      (rule Tpair j not_divides nu finalweight Tf)+
qed

end
