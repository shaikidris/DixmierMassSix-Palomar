theory Axis_Negative_Top_Mass
 imports Positive_Binomial_Mass_Bound
begin

lemma preliminary_axis_diagonal_negative_top_mass_ge_ten:
 fixes P Q::"complex poly_operator" and n::nat and e::"nat\<times>nat"
 assumes source: "GGVPreliminaryCompanionInput"
 and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
 and pair: "is_counterexample_pair P Q"
 and member: "(n,0)\<in>biv_support(leading_form 1 1 P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> d=(n,0)"
 and e: "e\<in>biv_support(pbw_symbol P)"
 and ey: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d\<le>snd e"
 and ex: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d=snd e \<Longrightarrow> fst d\<le>fst e"
 and negative: "pair_grade e<0"
 shows "10\<le>weyl_mass P"
proof -
 obtain sigma where sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
   using preliminary_axis_diagonal_positive_face[OF source pair member unique] by blast
 obtain lam alpha a b where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and b: "1\<le>b"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*b)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
   using preliminary_positive_face_binomial[OF source pair sigma face] by blast
 have bp: "0<b" using b by arith
 show ?thesis by (rule preliminary_positive_binomial_mass_of_negative_top_boundary[OF source bound pair sigma bp lam alpha degree shape e ey ex negative])
qed

end
