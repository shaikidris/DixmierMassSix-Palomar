theory Leading_Powers
 imports Global_Face_Power_Ratio "Weyl_Leading_Forms"
begin

lemma leadingForm_pow_succ:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and sum: "0<rho+sigma"
 and degree: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
 shows "weighted_degree rho sigma (pbw_symbol(P ^^ Suc n))=bot.Value(int(Suc n)*m) \<and>
 leading_form rho sigma (P ^^ Suc n)=(leading_form rho sigma P)^Suc n"
proof (induction n)
 case 0
 then show ?case using degree by simp
next
 case (Suc n)
 have carrier: "(P ^^ Suc n)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_power) (use P in \<open>simp add: weyl_algebra_def\<close>)
 have power_degree: "weighted_degree rho sigma (pbw_symbol(P ^^ Suc n))=bot.Value(int(Suc n)*m)"
   using Suc.IH by blast
 have power_face: "leading_form rho sigma (P ^^ Suc n)=(leading_form rho sigma P)^Suc n"
   using Suc.IH by blast
 have product:
   "weighted_degree rho sigma (pbw_symbol(op_comp P (P ^^ Suc n)))=bot.Value(m+int(Suc n)*m) \<and>
    leading_form rho sigma (op_comp P (P ^^ Suc n))=leading_form rho sigma P*leading_form rho sigma (P ^^ Suc n)"
   by (rule symbol_mul_degree_and_leading_form[OF P carrier sum degree power_degree])
 have operator_power: "op_comp P (P ^^ Suc n)=P ^^ Suc(Suc n)"
   by (simp add: op_comp_def fun_eq_iff)
 have integer_power: "m+int(Suc n)*m=int(Suc(Suc n))*m"
   by (simp add: algebra_simps)
 show ?case using product by (simp only: operator_power integer_power power_face)
   (simp add: power_Suc mult.commute)
qed

lemma leadingForm_smul:
 fixes P::"complex poly_operator" and c::complex
 assumes P: "P\<in>weyl_algebra" and c: "c\<noteq>0"
 and degree: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
 shows "weighted_degree rho sigma (pbw_symbol(\<lambda>p. smult c (P p)))=bot.Value m \<and>
 leading_form rho sigma (\<lambda>p. smult c (P p))=smult [:c:] (leading_form rho sigma P)"
proof -
 have symbol: "pbw_symbol(\<lambda>p. smult c (P p))=smult [:c:] (pbw_symbol P)"
   by (rule weyl_symbol_smult[OF P])
 have support: "biv_support(smult [:c:] (pbw_symbol P))=biv_support(pbw_symbol P)"
   using c by (auto simp: biv_support_def biv_coeff_def)
 have scalar_degree: "weighted_degree rho sigma (pbw_symbol(\<lambda>p. smult c (P p)))=bot.Value m"
   using degree by (simp only: symbol weighted_degree_def support)
 have vp: "v_degree rho sigma P=m" and vs: "v_degree rho sigma (\<lambda>p. smult c (P p))=m"
   by (simp_all add: v_degree_def degree scalar_degree)
 show ?thesis using scalar_degree
   by (simp add: leading_form_def vp vs symbol weighted_component_smult)
qed

lemma native_equal_top_face_degree_drop:
 fixes Q T::"complex poly_operator"
 assumes Q: "Q\<in>weyl_algebra" and T: "T\<in>weyl_algebra" and positive: "0<m"
 and Qdegree: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value m"
 and Tdegree: "weighted_degree rho sigma (pbw_symbol T)=bot.Value m"
 and face: "leading_form rho sigma Q=leading_form rho sigma T"
 shows "v_degree rho sigma (Q-T)<m"
proof -
 have symbol: "pbw_symbol(Q-T)=pbw_symbol Q-pbw_symbol T" by (rule weyl_symbol_sub[OF Q T])
 have bound: "weighted_degree rho sigma (pbw_symbol(Q-T))\<le>bot.Value m"
   unfolding symbol by (rule weighted_degree_diff_le) (simp_all add: Qdegree Tdegree)
 have vQ: "v_degree rho sigma Q=m" and vT: "v_degree rho sigma T=m"
   by (simp_all add: v_degree_def Qdegree Tdegree)
 have components: "weighted_component rho sigma m (pbw_symbol Q)=weighted_component rho sigma m (pbw_symbol T)"
   using face by (simp only: leading_form_def vQ vT)
 have zero: "weighted_component rho sigma m (pbw_symbol(Q-T))=0"
 proof (rule biv_eqI)
   fix i j
   have equality: "biv_coeff(weighted_component rho sigma m (pbw_symbol Q)) i j=
     biv_coeff(weighted_component rho sigma m (pbw_symbol T)) i j" using components by simp
   show "biv_coeff(weighted_component rho sigma m (pbw_symbol(Q-T))) i j=biv_coeff 0 i j"
     using equality by (auto simp: symbol weighted_component_coeff split: if_splits)
 qed
 have unequal: "weighted_degree rho sigma (pbw_symbol(Q-T))\<noteq>bot.Value m"
 proof
   assume degree: "weighted_degree rho sigma (pbw_symbol(Q-T))=bot.Value m"
   have nonzero: "weighted_component rho sigma m (pbw_symbol(Q-T))\<noteq>0"
     by (rule weighted_top_component_nonzero[OF degree])
   show False using nonzero zero by contradiction
 qed
 show ?thesis
 proof (cases "weighted_degree rho sigma (pbw_symbol(Q-T))")
   case Bot
   have degree_zero: "v_degree rho sigma (Q-T)=0"
     by (simp only: v_degree_def Bot; simp)
   show ?thesis using positive by (simp only: degree_zero)
 next
   case (Value n)
   have strict: "n<m" using bound unequal by (simp only: Value; simp)
   have degree_value: "v_degree rho sigma (Q-T)=n"
     by (simp only: v_degree_def Value; simp)
   show ?thesis using strict by (simp only: degree_value)
 qed
qed

lemma mateSubtraction_weight_drop_of_leadingForm_eq:
 fixes P Q::"complex poly_operator" and c::complex
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and positive: "0<m"
 and Qdegree: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value m"
 and Tdegree: "weighted_degree rho sigma (pbw_symbol(\<lambda>p. smult c ((P ^^ k) p)))=bot.Value m"
 and face: "leading_form rho sigma Q=leading_form rho sigma (\<lambda>p. smult c ((P ^^ k) p))"
 shows "v_degree rho sigma (Q-(\<lambda>p. smult c ((P ^^ k) p)))<m"
proof -
 have power_carrier: "(P ^^ k)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_power) (use P in \<open>simp add: weyl_algebra_def\<close>)
 have term_carrier: "(\<lambda>p. smult c ((P ^^ k) p))\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_smult) (use power_carrier in \<open>simp add: weyl_algebra_def\<close>)
 show ?thesis by (rule native_equal_top_face_degree_drop[OF Q term_carrier positive Qdegree Tdegree face])
qed

lemma mateSubtraction_weight_drop_of_power_face:
 fixes P Q::"complex poly_operator" and c::complex
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and c: "c\<noteq>0"
 and sum: "0<rho+sigma" and positive: "0<int(Suc n)*m"
 and Pdegree: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
 and Qdegree: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value(int(Suc n)*m)"
 and face: "leading_form rho sigma Q=smult [:c:] ((leading_form rho sigma P)^Suc n)"
 shows "v_degree rho sigma (Q-(\<lambda>p. smult c ((P ^^ Suc n) p)))<int(Suc n)*m"
proof -
 have power_carrier: "(P ^^ Suc n)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_power) (use P in \<open>simp add: weyl_algebra_def\<close>)
 have power_degree: "weighted_degree rho sigma (pbw_symbol(P ^^ Suc n))=bot.Value(int(Suc n)*m)"
 and power_face: "leading_form rho sigma (P ^^ Suc n)=(leading_form rho sigma P)^Suc n"
   using leadingForm_pow_succ[where n=n, OF P sum Pdegree] by auto
 have term_degree: "weighted_degree rho sigma (pbw_symbol(\<lambda>p. smult c ((P ^^ Suc n) p)))=bot.Value(int(Suc n)*m)"
 and term_face: "leading_form rho sigma (\<lambda>p. smult c ((P ^^ Suc n) p))=smult [:c:] (leading_form rho sigma (P ^^ Suc n))"
   using leadingForm_smul[OF power_carrier c power_degree] by auto
 have equal_face: "leading_form rho sigma Q=leading_form rho sigma (\<lambda>p. smult c ((P ^^ Suc n) p))"
   by (simp only: term_face power_face face)
 show ?thesis by (rule mateSubtraction_weight_drop_of_leadingForm_eq[OF P Q positive Qdegree term_degree equal_face])
qed

end
