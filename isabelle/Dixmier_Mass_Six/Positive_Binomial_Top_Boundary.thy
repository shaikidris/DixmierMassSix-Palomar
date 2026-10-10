theory Positive_Binomial_Top_Boundary
 imports "Diagonal_Binomial_Face"
   "Positive_Companion_Coordinates"
begin

lemma preliminary_positive_binomial_top_boundary:
 fixes P Q::"complex poly_operator" and sigma a b::nat and lam alpha::complex
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1\<le>sigma" and bp: "0<b" and lam: "lam\<noteq>0"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*b)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
 shows "(a,b)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). snd d\<le>b) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). snd d=b \<longrightarrow> fst d\<le>a)"
proof -
 have data: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P) \<and>
   (\<forall>d\<in>biv_support(leading_form 1 (int sigma) P). snd d\<le>b)"
   by (rule positive_binomial_top_face_point[OF lam degree shape])
 have member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)" using data by blast
 have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
   using member by (simp add: leading_form_def weighted_component_support)
 have upper: "\<forall>d\<in>biv_support(pbw_symbol P). snd d\<le>b"
   by (rule preliminary_positive_last_point_y_bound[OF source pair sigma member _ bp]) (use data in blast)
 have boundary: "fst d\<le>a" if d: "d\<in>biv_support(pbw_symbol P)" and height: "snd d=b" for d
 proof -
   have bound: "rationalNewtonWeight (of_int(int sigma)/ of_int(1::int)) d\<le>
     rationalNewtonWeight (of_int(int sigma)/ of_int(1::int)) (a,b)"
     using member d by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma="int sigma", OF zero_less_one]; blast)
   show ?thesis using bound by (simp add: rationalNewtonWeight_def height)
 qed
 show ?thesis using raw upper boundary by blast
qed

end
