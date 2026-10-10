theory Positive_Descent_Invariant
 imports "Positive_Shear_Monomial_Face"
   "Positive_Integer_Face"
begin

lemma preliminary_positive_binomial_at_top_point:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
 and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
 and upper: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d\<le>b"
 shows "\<exists>lam alpha::complex. lam\<noteq>0 \<and> alpha\<noteq>0 \<and>
   v_degree 1 (int sigma) P=int(a+sigma*b) \<and>
   leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
proof -
 obtain lam alpha a' k where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and kp: "1\<le>k"
 and degree: "v_degree 1 (int sigma) P=int(a'+sigma*k)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a'*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
   using preliminary_positive_face_binomial[OF source pair sigma face] by blast
 have data: "(a',k)\<in>biv_support(leading_form 1 (int sigma) P) \<and>
   (\<forall>d\<in>biv_support(leading_form 1 (int sigma) P). snd d\<le>k)"
   by (rule positive_binomial_top_face_point[OF lam degree shape])
 have bk: "b\<le>k" using data member by auto
 have raw: "(a',k)\<in>biv_support(pbw_symbol P)"
   using data by (auto simp: leading_form_def weighted_component_support)
 have kb: "k\<le>b" using upper[OF raw] by simp
 have keq: "k=b" using bk kb by arith
 have pointweight: "pair_weight 1 (int sigma) (a,b)=v_degree 1 (int sigma) P"
   using member by (simp add: leading_form_def weighted_component_support)
 have aeq: "a'=a" using pointweight degree keq by (simp add: pair_weight_def)
 show ?thesis using lam alpha degree shape keq aeq by blast
qed

end
