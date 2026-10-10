theory Positive_Shear_Finite_Descent
 imports Positive_Descent_Invariant
begin

lemma weighted_monomial_support:
 fixes lam::complex and a b::nat
 assumes lam: "lam\<noteq>0"
 shows "biv_support([:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b)={(a,b)}"
 by (simp only: native_weighted_monomial_eq weighted_support_monom[OF lam])

lemma preliminary_positive_descent_shear_step:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1\<le>sigma" and bp: "0<b"
 and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> d=(a,b)"
 and bad: "\<exists>d\<in>biv_support(pbw_symbol P). a+b<fst d+snd d"
 shows "\<exists>tau::nat. \<exists>R S::complex poly_operator. 1<tau \<and> tau<sigma \<and>
   is_counterexample_pair R S \<and> biv_support(leading_form 1 (int tau) R)={(a,b)}"
proof -
 have upper: "\<forall>d\<in>biv_support(pbw_symbol P). snd d\<le>b"
   by (rule preliminary_positive_last_point_y_bound[OF source pair sigma member _ bp]) (use unique in auto)
 obtain tau where tau: "1<tau" and small: "tau<sigma"
 and face: "in_direction 1 (int tau) P" and point: "(a,b)\<in>biv_support(leading_form 1 (int tau) P)"
   using preliminary_positive_singleton_next_integer_face[OF source pair sigma bp member unique bad] by blast
 obtain lam alpha where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
 and degree: "v_degree 1 (int tau) P=int(a+tau*b)"
 and shape: "leading_form 1 (int tau) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^tau)^b"
   using preliminary_positive_binomial_at_top_point[OF source pair tau face point] upper by blast
 have cut: "cut_poly 1 (int tau) P=[:lam:]*[:-alpha,1:]^b" by (rule positive_binomial_face_cut[OF shape])
 obtain R S where RS: "is_counterexample_pair R S"
 and mono: "leading_form 1 (int tau) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
   using polynomial_root_shear_monomial_face[OF pair degree cut] by blast
 have support: "biv_support(leading_form 1 (int tau) R)={(a,b)}"
   by (simp only: mono weighted_monomial_support[OF lam])
 show ?thesis using tau small RS support by blast
qed

lemma totalDeg_eq_of_support_sum_bound:
 fixes P::"complex poly_operator" and a b::nat
 assumes point: "(a,b)\<in>biv_support(pbw_symbol P)"
 and upper: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d+snd d\<le>a+b"
 shows "total_degree P=a+b"
proof -
 have lo: "a+b\<le>total_degree P" using support_total_degree_bound[OF point] by simp
 have hi: "total_degree P\<le>a+b"
   unfolding total_degree_def by (rule Max.boundedI) (use upper in auto)
 show ?thesis using lo hi by arith
qed

lemma preliminary_positive_singleton_finite_descent:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1\<le>sigma" and bp: "0<b"
 and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> d=(a,b)"
 shows "\<exists>R S::complex poly_operator. is_counterexample_pair R S \<and> total_degree R=a+b"
using pair sigma member unique
proof (induction sigma arbitrary: P Q rule: less_induct)
 case (less sigma)
 show ?case
 proof (cases "\<exists>d\<in>biv_support(pbw_symbol P). a+b<fst d+snd d")
   case True
   obtain tau R S where tau: "1<tau" and small: "tau<sigma" and RS: "is_counterexample_pair R S"
   and support: "biv_support(leading_form 1 (int tau) R)={(a,b)}"
     using preliminary_positive_descent_shear_step[OF source less.prems(1,2) bp less.prems(3,4) True] by blast
   have point: "(a,b)\<in>biv_support(leading_form 1 (int tau) R)" by (simp add: support)
   have only: "d=(a,b)" if "d\<in>biv_support(leading_form 1 (int tau) R)" for d
     using that by (simp add: support)
   show ?thesis by (rule less.IH[OF small RS _ point only]) (use tau in arith)
 next
   case False
   have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
     using less.prems(3) by (simp add: leading_form_def weighted_component_support)
   have upper: "fst d+snd d\<le>a+b" if "d\<in>biv_support(pbw_symbol P)" for d
     using False that by auto
   have degree: "total_degree P=a+b" by (rule totalDeg_eq_of_support_sum_bound[OF raw upper])
   show ?thesis using less.prems(1) degree by blast
 qed
qed

end
