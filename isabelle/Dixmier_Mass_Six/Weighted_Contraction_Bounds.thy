theory Weighted_Contraction_Bounds
  imports Weyl_Symbol_Product "Weighted_Degree_Bounds"
begin

lemma contraction_term_support_bound:
  assumes pos: "0<rho+sigma" and k: "k\<le>min (fst q) (snd p)" and ell: "ell\<le>k"
    and p: "pair_weight rho sigma p\<le>m" and q: "pair_weight rho sigma q\<le>n"
    and u: "u\<in>biv_support (contraction_term c d p q k)"
  shows "pair_weight rho sigma u\<le>m+n-int ell*(rho+sigma)"
proof -
  have ue: "u=(fst p+fst q-k,snd p+snd q-k)"
    using u by (auto simp: contraction_term_def biv_support_def prod_eq_iff split: if_splits)
  have w: "pair_weight rho sigma (fst p+fst q-k,snd p+snd q-k)+int k*(rho+sigma) =
    pair_weight rho sigma p+pair_weight rho sigma q"
    using normal_contraction_weight[OF k, of rho sigma "fst p" "snd q"]
    by (simp add: pair_weight_def algebra_simps)
  have drop: "int ell*(rho+sigma)\<le>int k*(rho+sigma)"
    by (rule mult_right_mono) (use ell pos in auto)
  show ?thesis using p q w drop by (simp only: ue; arith)
qed
lemma contraction_family_support_bound:
  assumes fs: "finite S" and ft: "finite T"
    and fk: "\<And>p q. p\<in>S \<Longrightarrow> q\<in>T \<Longrightarrow> finite (K p q)"
    and kb: "\<And>p q k. p\<in>S \<Longrightarrow> q\<in>T \<Longrightarrow> k\<in>K p q \<Longrightarrow> k\<le>min (fst q) (snd p) \<and> ell\<le>k"
    and pos: "0<rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p\<le>m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q\<le>n"
    and u: "u\<in>biv_support (\<Sum>p\<in>S. \<Sum>q\<in>T. \<Sum>k\<in>K p q. contraction_term c d p q k)"
  shows "pair_weight rho sigma u\<le>m+n-int ell*(rho+sigma)"
proof (rule biv_support_weight_sum[OF fs _ u])
  fix p u assume p: "p\<in>S" and u: "u\<in>biv_support (\<Sum>q\<in>T. \<Sum>k\<in>K p q. contraction_term c d p q k)"
  show "pair_weight rho sigma u\<le>m+n-int ell*(rho+sigma)"
  proof (rule biv_support_weight_sum[OF ft _ u])
    fix q v assume q: "q\<in>T" and v: "v\<in>biv_support (\<Sum>k\<in>K p q. contraction_term c d p q k)"
    show "pair_weight rho sigma v\<le>m+n-int ell*(rho+sigma)"
    proof (rule biv_support_weight_sum[OF fk[OF p q] _ v])
      fix k w assume k: "k\<in>K p q" and w: "w\<in>biv_support (contraction_term c d p q k)"
      have b: "k\<le>min (fst q) (snd p) \<and> ell\<le>k" by (rule kb[OF p q k])
      show "pair_weight rho sigma w\<le>m+n-int ell*(rho+sigma)"
        by (rule contraction_term_support_bound[OF pos b[THEN conjunct1] b[THEN conjunct2] cb[OF p] db[OF q] w])
    qed
  qed
qed
lemma pbw_product_support_bound:
  assumes fs: "finite S" and ft: "finite T" and pos: "0<rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p\<le>m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q\<le>n"
    and u: "u\<in>biv_support (pbw_product_polynomial S T c d)"
  shows "pair_weight rho sigma u\<le>m+n"
proof -
  have h: "pair_weight rho sigma u\<le>m+n-int 0*(rho+sigma)"
    by (rule contraction_family_support_bound[OF fs ft _ _ pos cb db u[unfolded pbw_product_polynomial_def]]) auto
  then show ?thesis by simp
qed
lemma higher_contraction_support_bound:
  assumes fs: "finite S" and ft: "finite T" and pos: "0<rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p\<le>m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q\<le>n"
    and u: "u\<in>biv_support (higher_contraction_polynomial S T c d)"
  shows "pair_weight rho sigma u\<le>m+n-(rho+sigma)"
proof -
  have fin: "finite {k::nat. k\<le>min (fst q) (snd p) \<and> 1<k}" for p q
    by (rule finite_subset[of _ "{..min (fst q) (snd p)}"]) auto
  have h: "pair_weight rho sigma u\<le>m+n-int 1*(rho+sigma)"
    by (rule contraction_family_support_bound[OF fs ft _ _ pos cb db u[unfolded higher_contraction_polynomial_def]])
       (auto intro: fin)
  then show ?thesis by simp
qed

lemma poisson_support_bound:
  assumes p: "\<And>u. u\<in>biv_support p \<Longrightarrow> pair_weight rho sigma u\<le>m"
    and q: "\<And>u. u\<in>biv_support q \<Longrightarrow> pair_weight rho sigma u\<le>n"
    and u: "u\<in>biv_support (biv_poisson p q)"
  shows "pair_weight rho sigma u\<le>m+n-(rho+sigma)"
proof -
  have first: "pair_weight rho sigma v\<le>m+n-(rho+sigma)" if "v\<in>biv_support (biv_dy p*biv_dx q)" for v
  proof -
    have "pair_weight rho sigma v\<le>(m-sigma)+(n-rho)"
      by (rule biv_support_weight_product[OF biv_dy_support_weight[OF p] biv_dx_support_weight[OF q] that])
    then show ?thesis by arith
  qed
  have second: "pair_weight rho sigma v\<le>m+n-(rho+sigma)" if "v\<in>biv_support (biv_dx p*biv_dy q)" for v
  proof -
    have "pair_weight rho sigma v\<le>(m-rho)+(n-sigma)"
      by (rule biv_support_weight_product[OF biv_dx_support_weight[OF p] biv_dy_support_weight[OF q] that])
    then show ?thesis by arith
  qed
  show ?thesis by (rule biv_support_weight_diff[OF first second u[unfolded biv_poisson_def]])
qed

lemma pbw_commutator_support_bound:
  assumes fs: "finite S" and ft: "finite T" and pos: "0<rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p\<le>m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q\<le>n"
    and u: "u\<in>biv_support (pbw_product_polynomial S T c d-pbw_product_polynomial T S d c)"
  shows "pair_weight rho sigma u\<le>m+n-(rho+sigma)"
proof -
  have cp: "\<And>v. v\<in>biv_support (coordinate_polynomial S c) \<Longrightarrow> pair_weight rho sigma v\<le>m"
    by (rule coordinate_polynomial_support_bound[OF cb])
  have dp: "\<And>v. v\<in>biv_support (coordinate_polynomial T d) \<Longrightarrow> pair_weight rho sigma v\<le>n"
    by (rule coordinate_polynomial_support_bound[OF db])
  have first: "\<And>v. v\<in>biv_support (biv_poisson (coordinate_polynomial S c) (coordinate_polynomial T d)) \<Longrightarrow> pair_weight rho sigma v\<le>m+n-(rho+sigma)"
    by (rule poisson_support_bound[OF cp dp])
  have h1: "\<And>v. v\<in>biv_support (higher_contraction_polynomial S T c d) \<Longrightarrow> pair_weight rho sigma v\<le>m+n-(rho+sigma)"
    by (rule higher_contraction_support_bound[OF fs ft pos cb db])
  have h2: "pair_weight rho sigma v\<le>m+n-(rho+sigma)" if "v\<in>biv_support (higher_contraction_polynomial T S d c)" for v
    using higher_contraction_support_bound[OF ft fs pos db cb that] by (simp only: add.commute)
  have diff: "\<And>v. v\<in>biv_support (higher_contraction_polynomial S T c d-higher_contraction_polynomial T S d c) \<Longrightarrow> pair_weight rho sigma v\<le>m+n-(rho+sigma)"
    by (rule biv_support_weight_diff[OF h1 h2])
  show ?thesis by (rule biv_support_weight_add[OF first diff u[unfolded pbw_product_commutator]])
qed

lemma weyl_pair_coordinate_data:
  fixes P Q :: "'a::field_char_0 poly_operator"
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
  shows "\<exists>S T c d. finite S \<and> finite T \<and> finite_normal_sum S c=P \<and> finite_normal_sum T d=Q \<and>
    (\<forall>u\<in>S. pair_weight rho sigma u\<le>m) \<and> (\<forall>u\<in>T. pair_weight rho sigma u\<le>n)"
proof -
  obtain c where fc: "finite {u. c u\<noteq>0}" and pc: "finite_normal_sum {u. c u\<noteq>0} c=P"
    and sc: "biv_support (pbw_symbol P)={u. c u\<noteq>0}"
    using symbol_support_finite_expansion[OF P] by blast
  obtain d where fd: "finite {u. d u\<noteq>0}" and qc: "finite_normal_sum {u. d u\<noteq>0} d=Q"
    and sd: "biv_support (pbw_symbol Q)={u. d u\<noteq>0}"
    using symbol_support_finite_expansion[OF Q] by blast
  have cb: "\<forall>u\<in>{u. c u\<noteq>0}. pair_weight rho sigma u\<le>m"
    by (intro ballI; rule weighted_degree_support_bound[OF pd]) (simp only: sc)
  have db: "\<forall>u\<in>{u. d u\<noteq>0}. pair_weight rho sigma u\<le>n"
    by (intro ballI; rule weighted_degree_support_bound[OF qd]) (simp only: sd)
  show ?thesis
    by (rule exI[of _ "{u. c u\<noteq>0}"]; rule exI[of _ "{u. d u\<noteq>0}"];
        rule exI[of _ c]; rule exI[of _ d]) (use fc fd pc qc cb db in blast)
qed

end
