theory Positive_Shear_Mate_Descent
 imports "Positive_Shear_Finite_Descent"
   "Polynomial_Shear_Top_Row"
begin

lemma preliminary_positive_descent_shear_step_with_mate_row:
 fixes P Q::"complex poly_operator" and sigma a b c d::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and sigma: "1\<le>sigma" and b: "0<b"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
   and bad: "\<exists>e\<in>biv_support(pbw_symbol P). a+b<fst e+snd e"
   and Qbound: "\<And>e. e\<in>biv_support(pbw_symbol Q) \<Longrightarrow> snd e\<le>d"
   and Qpoint: "(c,d)\<in>biv_support(pbw_symbol Q)"
 shows "\<exists>tau R S. 1<tau \<and> tau<sigma \<and> is_counterexample_pair R S \<and>
   biv_support(leading_form 1 (int tau) R)={(a,b)} \<and>
   (\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d) \<and> (c,d)\<in>biv_support(pbw_symbol S)"
proof -
 have upper: "\<forall>e\<in>biv_support(pbw_symbol P). snd e\<le>b"
   by (rule preliminary_positive_last_point_y_bound[OF source pair sigma member _ b]) (use unique in auto)
 obtain tau where tau: "1<tau" and smaller: "tau<sigma"
   and face: "in_direction 1 (int tau) P" and point: "(a,b)\<in>biv_support(leading_form 1 (int tau) P)"
   using preliminary_positive_singleton_next_integer_face[OF source pair sigma b member unique bad] by blast
 obtain lam alpha where lam: "lam\<noteq>0"
   and degree: "v_degree 1 (int tau) P=int(a+tau*b)"
   and shape: "leading_form 1 (int tau) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^tau)^b"
   using preliminary_positive_binomial_at_top_point[OF source pair tau face point] upper by blast
 obtain R S where RS: "is_counterexample_pair R S"
   and recoverR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int tau) alpha (polynomial_ramified_lift 1 P)"
   and recoverS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 (int tau) alpha (polynomial_ramified_lift 1 Q)"
   using polynomial_monomial_cut_recovers_polynomial_counterexample[OF pair, where sigma=tau and c=alpha] by blast
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
   using pair RS by (simp_all add: is_counterexample_pair_def)
 have direction: "is_direction 1 (int tau)" by (simp add: is_direction_def)
 have Ppositive: "0<v_degree 1 (int tau) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Rpositive: "0<v_degree 1 (int tau) R" by (rule counterexample_vDeg_pos_all_directions[OF RS direction])
 have Pnz: "P\<noteq>0" using Ppositive by auto
 have transport: "v_degree 1 (int tau) R=v_degree 1 (int tau) P \<and>
   cut_poly 1 (int tau) R=pcompose (cut_poly 1 (int tau) P) [:alpha,1:]"
   by (rule polynomial_monomial_cut_weight_and_translate[OF P R Pnz Ppositive Rpositive recoverR])
 have oldcut: "cut_poly 1 (int tau) P=[:lam:]*[:-alpha,1:]^b"
   by (rule positive_binomial_face_cut[OF shape])
 have affine: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have newcut: "cut_poly 1 (int tau) R=[:lam:]*[:0,1:]^b"
   using conjunct2[OF transport] by (simp add: oldcut pcompose_smult native_pcompose_power affine)
 have Rdegree: "v_degree 1 (int tau) R=int(a+tau*b)" using transport degree by simp
 have mono: "leading_form 1 (int tau) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
   using positive_face_eq_of_linear_power_cut[OF Rdegree, where lam=lam and alpha=0] newcut by simp
 have support: "biv_support(leading_form 1 (int tau) R)={(a,b)}"
   by (simp only: mono weighted_monomial_support[OF lam])
 have bound: "\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d"
   using polynomial_cut_preserves_y_bound_and_top_row[OF Q S Qbound recoverS] by blast
 have retained: "(c,d)\<in>biv_support(pbw_symbol S)"
   by (rule polynomial_cut_preserves_top_row_point[OF Q S Qbound Qpoint recoverS])
 show ?thesis by (intro exI[of _ tau] exI[of _ R] exI[of _ S])
   (use tau smaller RS support bound retained in blast)
qed

lemma preliminary_positive_singleton_finite_descent_with_mate_row:
 fixes P Q::"complex poly_operator" and sigma a b c d::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and sigma: "1\<le>sigma" and b: "0<b"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
   and Qbound: "\<And>e. e\<in>biv_support(pbw_symbol Q) \<Longrightarrow> snd e\<le>d"
   and Qpoint: "(c,d)\<in>biv_support(pbw_symbol Q)"
 shows "\<exists>R S. is_counterexample_pair R S \<and> total_degree R=a+b \<and>
   (a,b)\<in>biv_support(pbw_symbol R) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d) \<and> (c,d)\<in>biv_support(pbw_symbol S)"
 using pair sigma member unique Qbound Qpoint
proof (induction sigma arbitrary: P Q rule: less_induct)
 case (less sigma)
 show ?case
 proof (cases "\<exists>e\<in>biv_support(pbw_symbol P). a+b<fst e+snd e")
   case True
   obtain tau R S where tau: "1<tau" and smaller: "tau<sigma" and RS: "is_counterexample_pair R S"
     and support: "biv_support(leading_form 1 (int tau) R)={(a,b)}"
     and bound: "\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d" and retained: "(c,d)\<in>biv_support(pbw_symbol S)"
     using preliminary_positive_descent_shear_step_with_mate_row[OF source less.prems(1,2) b less.prems(3,4) True less.prems(5,6)] by blast
   have occupied: "(a,b)\<in>biv_support(leading_form 1 (int tau) R)" by (simp add: support)
   have only: "e=(a,b)" if "e\<in>biv_support(leading_form 1 (int tau) R)" for e
     using that by (simp add: support)
   show ?thesis by (rule less.IH[OF smaller RS _ occupied only _ retained]) (use tau bound in auto)
 next
   case False
   have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
     using less.prems(3) by (simp add: leading_form_def weighted_component_support)
   have upper: "fst e+snd e\<le>a+b" if "e\<in>biv_support(pbw_symbol P)" for e using False that by auto
   have degree: "total_degree P=a+b" by (rule totalDeg_eq_of_support_sum_bound[OF raw upper])
   have bound: "\<forall>e\<in>biv_support(pbw_symbol Q). snd e\<le>d"
     by (intro ballI) (rule less.prems(5))
   show ?thesis
   proof (rule exI[of _ P], rule exI[of _ Q], intro conjI)
     show "is_counterexample_pair P Q" by (rule less.prems(1))
     show "total_degree P=a+b" by (rule degree)
     show "(a,b)\<in>biv_support(pbw_symbol P)" by (rule raw)
     show "\<forall>e\<in>biv_support(pbw_symbol Q). snd e\<le>d" by (rule bound)
     show "(c,d)\<in>biv_support(pbw_symbol Q)" by (rule less.prems(6))
   qed
 qed
qed

end
