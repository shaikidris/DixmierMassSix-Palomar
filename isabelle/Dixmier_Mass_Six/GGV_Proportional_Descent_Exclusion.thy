theory GGV_Proportional_Descent_Exclusion
 imports "Degree_Minimal_Pair"
   "Positive_Singleton_Mate_Face"
begin

lemma proportional_positive_degree_gcd_drop:
 fixes sigma a b c d::nat
 assumes slope: "1<sigma" and positive: "0<b" and proportional: "a*d=b*c"
 shows "gcd (a+b) (c+d)<gcd (a+sigma*b) (c+sigma*d)"
proof -
 have scaled: "sigma*(a*d)=sigma*(b*c)" by (rule arg_cong[OF proportional])
 have ratio: "(a+sigma*b)*(c+d)=(a+b)*(c+sigma*d)"
   using proportional scaled by (simp add: algebra_simps)
 have scale: "(a+b)*gcd (a+sigma*b) (c+sigma*d)=
   (a+sigma*b)*gcd (a+b) (c+d)"
 proof -
   have "(a+b)*gcd (a+sigma*b) (c+sigma*d)=
     gcd ((a+b)*(a+sigma*b)) ((a+b)*(c+sigma*d))"
     by (simp only: gcd_mult_left; simp)
   also have "...=gcd ((a+sigma*b)*(a+b)) ((a+sigma*b)*(c+d))"
     by (simp only: ratio[symmetric] mult.commute[of "a+b" "a+sigma*b"])
   also have "...=(a+sigma*b)*gcd (a+b) (c+d)" by (simp only: gcd_mult_left; simp)
   finally show ?thesis .
 qed
 have gcd_positive: "0<gcd (a+b) (c+d)" using positive by simp
 have increase: "b<sigma*b"
   using mult_strict_right_mono[OF slope positive] by simp
 have degree_increase: "a+b<a+sigma*b" using increase by arith
 show ?thesis
 proof (rule ccontr)
   assume "\<not>gcd (a+b) (c+d)<gcd (a+sigma*b) (c+sigma*d)"
   then have le: "gcd (a+sigma*b) (c+sigma*d)\<le>gcd (a+b) (c+d)" by arith
   have weak: "(a+b)*gcd (a+sigma*b) (c+sigma*d)\<le>(a+b)*gcd (a+b) (c+d)"
     by (rule mult_left_mono[OF le]) simp
   have strict: "(a+b)*gcd (a+b) (c+d)<(a+sigma*b)*gcd (a+b) (c+d)"
     by (rule mult_strict_right_mono[OF degree_increase gcd_positive])
   show False using weak strict scale by arith
 qed
qed

lemma degreeMinimal_proportional_positive_descent_impossible:
 fixes P Q R S::"complex poly_operator" and sigma a b::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and recovered: "is_counterexample_pair R S" and sigma: "1<sigma" and b: "0<b"
   and Pdegree: "total_degree P=a+sigma*b"
   and Qdegree: "total_degree Q=nat(v_degree 1 (int sigma) S)"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) R)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) R) \<Longrightarrow> e=(a,b)"
 shows False
proof -
 have slope: "1\<le>sigma" using sigma by arith
 obtain c d T U where d: "0<d" and proportional: "a*d=b*c"
   and weight: "v_degree 1 (int sigma) S=int(c+sigma*d)"
   and pair: "is_counterexample_pair T U" and Tdegree: "total_degree T=a+b" and Udegree: "total_degree U=c+d"
   using counterexample_positive_singleton_finite_descent_pair[OF recovered slope b member unique] by blast
 have Qtotal: "total_degree Q=c+sigma*d" by (simp only: Qdegree weight nat_int)
 have least: "gcd(total_degree P)(total_degree Q)\<le>gcd(total_degree T)(total_degree U)"
   using minimal pair by (simp add: is_degree_minimal_counterexample_pair_def)
 have drop: "gcd (a+b) (c+d)<gcd (a+sigma*b) (c+sigma*d)"
   by (rule proportional_positive_degree_gcd_drop[OF sigma b proportional])
 show False using least drop by (simp only: Pdegree Qtotal Tdegree Udegree; arith)
qed

end
