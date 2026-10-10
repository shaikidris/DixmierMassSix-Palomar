theory Joseph_Commutator_Chain
  imports "Generated_Face_Filtration"
begin

primrec josephCommutatorChain :: "complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow> nat \<Rightarrow> complex poly_operator" where
  "josephCommutatorChain P R 0=R"
| "josephCommutatorChain P R (Suc n)=op_comp P (josephCommutatorChain P R n)-op_comp (josephCommutatorChain P R n) P"

lemma josephCommutatorChain_mem:
  assumes "R\<in>op_adjoin {P,Q}"
  shows "josephCommutatorChain P R n\<in>op_adjoin {P,Q}"
  using assms by (induction n) (auto intro: op_adjoin.diff op_adjoin.comp op_adjoin.generator)

lemma josephCommutatorChain_weyl:
  assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
  shows "josephCommutatorChain P R n\<in>weyl_algebra"
  using R by (induction n)
    (auto simp: weyl_algebra_def intro: op_adjoin.diff op_adjoin.comp P[unfolded weyl_algebra_def])

lemma joseph_chain_zero:
  assumes P: "poly_linear P"
  shows "josephCommutatorChain P 0 n=0"
  by (induction n) (auto simp: op_comp_def fun_eq_iff poly_linear_zero_image[OF P])

lemma joseph_chain_add:
  assumes P: "poly_linear P"
  shows "josephCommutatorChain P (R+S) n=josephCommutatorChain P R n+josephCommutatorChain P S n"
  by (induction n) (auto simp: op_comp_def fun_eq_iff P[unfolded poly_linear_def] algebra_simps)

lemma joseph_linear_neg_image:
  assumes P: "poly_linear P"
  shows "P (-x)= -P x"
proof -
  have scalar: "P (smult (-1) x)=smult (-1) (P x)"
    by (rule spec[OF spec[OF conjunct2[OF P[unfolded poly_linear_def]], of "-1"], of x])
  show ?thesis using scalar by (simp only: smult_minus_left smult_1_left)
qed

lemma joseph_linear_diff_image:
  assumes P: "poly_linear P"
  shows "P (x-y)=P x-P y"
proof -
  have neg: "P (-y)= -P y" by (rule joseph_linear_neg_image[OF P])
  have add: "P (u+v)=P u+P v" for u v
    by (rule spec[OF spec[OF conjunct1[OF P[unfolded poly_linear_def]], of u], of v])
  show ?thesis
  proof -
    have "P (x-y)=P (x+(-y))" by (simp only: diff_conv_add_uminus)
    also have "...=P x+P (-y)" by (rule add)
    also have "...=P x-P y" by (simp only: neg diff_conv_add_uminus)
    finally show ?thesis .
  qed
qed

lemma joseph_chain_diff:
  assumes P: "poly_linear P"
  shows "josephCommutatorChain P (R-S) n=josephCommutatorChain P R n-josephCommutatorChain P S n"
proof -
  have decomposition: "R=S+(R-S)" by simp
  have transport: "josephCommutatorChain P R n=josephCommutatorChain P (S+(R-S)) n"
    using decomposition by (rule arg_cong)
  have sum: "josephCommutatorChain P R n=josephCommutatorChain P S n+josephCommutatorChain P (R-S) n"
    using transport by (simp only: joseph_chain_add[OF P])
  have cancel: "josephCommutatorChain P R n-josephCommutatorChain P S n=josephCommutatorChain P (R-S) n"
    by (simp only: sum) simp
  show ?thesis by (rule sym[OF cancel])
qed

lemma joseph_chain_comp:
  "josephCommutatorChain P R (n+m)=josephCommutatorChain P (josephCommutatorChain P R m) n"
  by (induction n) simp_all

lemma joseph_chain_shift:
  "josephCommutatorChain P (op_comp P R-op_comp R P) n=josephCommutatorChain P R (Suc n)"
  using joseph_chain_comp[of P R n 1] by simp

lemma joseph_two_bracket_of_terminating_chain:
  fixes P Q R :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
    and weight: "0<rho+sigma" and adjoin: "R\<in>op_adjoin {P,Q}"
    and first: "biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0"
    and terminal: "\<exists>n. josephCommutatorChain P R n=0"
  shows "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and>
    biv_poisson (leading_form rho sigma P) (leading_form rho sigma T)\<noteq>0 \<and>
    biv_poisson (leading_form rho sigma P)
      (biv_poisson (leading_form rho sigma P) (leading_form rho sigma T))=0"
proof -
  let ?B = "\<lambda>n. biv_poisson (leading_form rho sigma P)
    (leading_form rho sigma (josephCommutatorChain P R n))"
  obtain terminal_n where killed: "josephCommutatorChain P R terminal_n=0" using terminal by blast
  have zero_leading: "leading_form rho sigma (0::complex poly_operator)=0"
    by (simp only: leading_form_def pbw_symbol_zero weighted_component_zero)
  have zero_bracket: "?B terminal_n=0"
    by (simp only: killed zero_leading) (simp add: biv_poisson_def)
  have exists: "\<exists>n. ?B n=0" by (rule exI[of _ terminal_n]) (rule zero_bracket)
  let ?N = "LEAST n. ?B n=0"
  have N: "?B ?N=0" by (rule LeastI_ex[OF exists])
  have Npos: "0<?N" using N first by (cases ?N) auto
  have prev: "?B (?N-1)\<noteq>0"
  proof
    assume zero: "?B (?N-1)=0"
    have "?N\<le>?N-1"
      by (rule Least_le[where P="\<lambda>n. ?B n=0" and k="?N-1"]) (rule zero)
    then show False using Npos by arith
  qed
  let ?T = "josephCommutatorChain P R (?N-1)"
  have T: "?T\<in>weyl_algebra" by (rule josephCommutatorChain_weyl[OF P R])
  have lead: "leading_form rho sigma (op_comp P ?T-op_comp ?T P)=
    biv_poisson (leading_form rho sigma P) (leading_form rho sigma ?T)"
    using leading_form_commutator[OF T P weight prev] by blast
  have next_chain: "josephCommutatorChain P R ?N=op_comp P ?T-op_comp ?T P"
  proof -
    have index: "?N=Suc (?N-1)" using Npos by arith
    show ?thesis by (subst (1) index) (rule josephCommutatorChain.simps)
  qed
  have second: "biv_poisson (leading_form rho sigma P)
    (biv_poisson (leading_form rho sigma P) (leading_form rho sigma ?T))=0"
    using N by (simp only: next_chain lead)
  show ?thesis by (intro exI[of _ ?T] conjI T josephCommutatorChain_mem[OF adjoin] prev second)
qed

end
