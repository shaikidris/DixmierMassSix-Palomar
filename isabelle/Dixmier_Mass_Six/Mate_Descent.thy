theory Mate_Descent
 imports Global_Face_Power_Ratio
begin

lemma native_power_commutes:
 "(P ^^ k)(P p)=P((P ^^ k) p)"
proof -
 have "(P ^^ Suc k) p=(P ^^ k)(P p)" by (simp only: funpow_Suc_right comp_apply)
 moreover have "(P ^^ Suc k) p=P((P ^^ k) p)" by simp
 ultimately show ?thesis by simp
qed

lemma mateSubtraction_commutator:
 fixes P Q::"complex poly_operator" and c::complex
 assumes P: "P\<in>weyl_algebra"
 shows "op_comp (Q-(\<lambda>p. smult c ((P ^^ k) p))) P-
 op_comp P (Q-(\<lambda>p. smult c ((P ^^ k) p)))= op_comp Q P- op_comp P Q"
proof (rule ext)
 fix p
 have linear: "poly_linear P" by (rule weyl_linear[OF P])
 have difference: "P(a-b)=P a-P b" for a b
 proof -
   have add: "P(a+(-b))=P a+P(-b)" using linear unfolding poly_linear_def by blast
   show ?thesis using add by (simp only: diff_conv_add_uminus affine_linear_neg_image[OF linear])
 qed
 have scalar: "P(smult c a)=smult c (P a)" for a using linear unfolding poly_linear_def by blast
 show "(op_comp (Q-(\<lambda>p. smult c ((P ^^ k) p))) P-
 op_comp P (Q-(\<lambda>p. smult c ((P ^^ k) p)))) p=(op_comp Q P- op_comp P Q) p"
   by (simp add: op_comp_def difference scalar native_power_commutes algebra_simps)
qed

lemma mateSubtraction_adjoin:
 fixes P Q::"complex poly_operator" and c::complex
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "op_adjoin {P,Q-(\<lambda>p. smult c ((P ^^ k) p))}= op_adjoin {P,Q}"
proof -
 let ?term="\<lambda>p. smult c ((P ^^ k) p)"
 let ?S="op_adjoin {P,Q}" let ?T="op_adjoin {P,Q-?term}"
 have pow_carrier: "(P ^^ k)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_power) (use P in \<open>simp add: weyl_algebra_def\<close>)
 have term_carrier: "?term\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_smult) (use pow_carrier in \<open>simp add: weyl_algebra_def\<close>)
 have sub_carrier: "Q-?term\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin.diff) (use Q term_carrier in \<open>simp_all add: weyl_algebra_def\<close>)
 have closedS: "op_subalgebra ?S" by (rule op_adjoin_subalgebra) (use P Q in \<open>auto intro: weyl_linear\<close>)
 have closedT: "op_subalgebra ?T" by (rule op_adjoin_subalgebra) (use P sub_carrier in \<open>auto intro: weyl_linear\<close>)
 have PS: "P\<in>?S" and QS: "Q\<in>?S" and PT: "P\<in>?T" and QT: "Q-?term\<in>?T"
   by (auto intro: op_adjoin.generator)
 have termS: "?term\<in>?S" by (rule op_adjoin_smult, rule op_adjoin_power, rule PS)
 have subS: "Q-?term\<in>?S" by (rule op_adjoin.diff[OF QS termS])
 have termT: "?term\<in>?T" by (rule op_adjoin_smult, rule op_adjoin_power, rule PT)
 have recovered: "Q\<in>?T" using op_adjoin.add[OF QT termT] by simp
 show ?thesis by (rule equalityI; rule op_adjoin_least)
   (use PS subS closedS PT recovered closedT in auto)
qed

lemma isCounterexamplePair_mateSubtraction:
 fixes P Q::"complex poly_operator" and c::complex
 assumes pair: "is_counterexample_pair P Q"
 shows "is_counterexample_pair P (Q-(\<lambda>p. smult c ((P ^^ k) p)))"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id" and nongeneration: "op_adjoin{P,Q}\<noteq>weyl_algebra"
   using pair by (auto simp: is_counterexample_pair_def)
 have power: "(P ^^ k)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_power) (use P in \<open>simp add: weyl_algebra_def\<close>)
 have power_term: "(\<lambda>p. smult c ((P ^^ k) p))\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_smult) (use power in \<open>simp add: weyl_algebra_def\<close>)
 have sub: "Q-(\<lambda>p. smult c ((P ^^ k) p))\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin.diff) (use Q power_term in \<open>simp_all add: weyl_algebra_def\<close>)
 show ?thesis using P sub exact nongeneration
   by (simp add: is_counterexample_pair_def mateSubtraction_commutator[OF P] mateSubtraction_adjoin[OF P Q])
qed

end
