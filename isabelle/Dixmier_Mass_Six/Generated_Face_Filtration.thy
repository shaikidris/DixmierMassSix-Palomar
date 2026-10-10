theory Generated_Face_Filtration
  imports Signed_Weight_Filtration
begin

lemma filtered_symbol_component_eq_leadingForm:
  fixes T :: "complex poly_operator"
  assumes hb: "pbw_symbol T\<in>signedWeightBelow rho sigma (b+1)"
    and hne: "weighted_component rho sigma b (pbw_symbol T)\<noteq>0"
  shows "weighted_component rho sigma b (pbw_symbol T)=leading_form rho sigma T"
proof -
  have bound: "pair_weight rho sigma u\<le>b" if mem: "u\<in>biv_support (pbw_symbol T)" for u
  proof (rule ccontr)
    assume "\<not>pair_weight rho sigma u\<le>b"
    then have "b+1\<le>pair_weight rho sigma u" by arith
    then have "biv_coeff (pbw_symbol T) (fst u) (snd u)=0"
      using hb by (simp add: signedWeightBelow_def)
    then show False using mem by (simp add: biv_support_def)
  qed
  have degree: "weighted_degree rho sigma (pbw_symbol T)=bot.Value b"
    by (rule weighted_degree_eq_of_support_bound_component[where p="pbw_symbol T", OF bound hne])
  have vd: "v_degree rho sigma T=b" by (simp add: v_degree_def degree)
  show ?thesis by (simp only: leading_form_def vd)
qed

lemma generated_face_centralization_implies_filtered_component:
  fixes P Q T :: "complex poly_operator" and f :: "complex bivariate"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and T: "T\<in>weyl_algebra"
    and hc: "\<And>R. R\<in>weyl_algebra \<Longrightarrow> R\<in>op_adjoin {P,Q} \<Longrightarrow> biv_poisson f (leading_form rho sigma R)=0"
    and hT: "T\<in>op_adjoin {P,Q}"
    and hb: "pbw_symbol T\<in>signedWeightBelow rho sigma (b+1)"
  shows "biv_poisson f (weighted_component rho sigma b (pbw_symbol T))=0"
proof (cases "weighted_component rho sigma b (pbw_symbol T)=0")
  case True
  show ?thesis by (simp add: True biv_poisson_def)
next
  case False
  show ?thesis by (simp only: filtered_symbol_component_eq_leadingForm[OF hb False]) (rule hc[OF T hT])
qed

end
