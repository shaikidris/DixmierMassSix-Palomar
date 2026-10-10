theory Weyl_Grade_Convolution
  imports "Weyl_Leading_Forms"
begin

lemma pbw_product_support_witness:
  assumes mem: "u\<in>biv_support (pbw_product_polynomial S T c d)"
  shows "\<exists>p\<in>S. \<exists>q\<in>T. \<exists>k\<le>min (fst q) (snd p).
    u=(fst p+fst q-k,snd p+snd q-k)"
proof -
  have nz: "(\<Sum>p\<in>S. \<Sum>q\<in>T. \<Sum>k\<le>min (fst q) (snd p).
      biv_coeff (contraction_term c d p q k) (fst u) (snd u)) \<noteq> 0"
    using mem by (simp add: biv_support_def pbw_product_polynomial_def biv_coeff_sum)
  obtain p where p: "p\<in>S" and nzp: "(\<Sum>q\<in>T. \<Sum>k\<le>min (fst q) (snd p).
      biv_coeff (contraction_term c d p q k) (fst u) (snd u)) \<noteq> 0"
    by (rule sum.not_neutral_contains_not_neutral[OF nz])
  obtain q where q: "q\<in>T" and nzq: "(\<Sum>k\<le>min (fst q) (snd p).
      biv_coeff (contraction_term c d p q k) (fst u) (snd u)) \<noteq> 0"
    by (rule sum.not_neutral_contains_not_neutral[OF nzp])
  obtain k where k: "k\<in>{..min (fst q) (snd p)}" and nzk: "biv_coeff (contraction_term c d p q k) (fst u) (snd u)\<noteq>0"
    by (rule sum.not_neutral_contains_not_neutral[OF nzq])
  have ue: "u=(fst p+fst q-k,snd p+snd q-k)"
    using nzk by (auto simp: contraction_term_def prod_eq_iff split: if_splits)
  show ?thesis by (rule bexI[of _ p], rule bexI[of _ q], rule exI[of _ k]) (use p q k ue in auto)
qed
lemma contraction_preserves_grade:
  assumes "k\<le>min (fst q) (snd p)"
  shows "pair_grade (fst p+fst q-k,snd p+snd q-k)=pair_grade p+pair_grade q"
  using normal_contraction_weight[OF assms, of 1 "-1" "fst p" "snd q"]
  by (simp add: pair_weight_def pair_grade_def algebra_simps)
lemma symbol_mul_grade_decomposition:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and u: "u\<in>biv_support (pbw_symbol (op_comp P Q))"
  shows "\<exists>p\<in>biv_support (pbw_symbol P). \<exists>q\<in>biv_support (pbw_symbol Q).
    pair_grade u=pair_grade p+pair_grade q"
proof -
  obtain c where fc: "finite {u. c u\<noteq>0}" and pc: "finite_normal_sum {u. c u\<noteq>0} c=P"
    and sc: "biv_support (pbw_symbol P)={u. c u\<noteq>0}"
    using symbol_support_finite_expansion[OF P] by blast
  obtain d where fd: "finite {u. d u\<noteq>0}" and qc: "finite_normal_sum {u. d u\<noteq>0} d=Q"
    and sd: "biv_support (pbw_symbol Q)={u. d u\<noteq>0}"
    using symbol_support_finite_expansion[OF Q] by blast
  have pq: "pbw_symbol (op_comp P Q)=pbw_product_polynomial {u. c u\<noteq>0} {u. d u\<noteq>0} c d"
    using symbol_composition_finite_coordinates[OF fc fd, of c d] by (simp only: pc qc)
  obtain p q k where p: "p\<in>{u. c u\<noteq>0}" and q: "q\<in>{u. d u\<noteq>0}"
    and k: "k\<le>min (fst q) (snd p)" and ue: "u=(fst p+fst q-k,snd p+snd q-k)"
    using pbw_product_support_witness[OF u[unfolded pq]] by blast
  have grade: "pair_grade u=pair_grade p+pair_grade q"
    unfolding ue by (rule contraction_preserves_grade[OF k])
  show ?thesis unfolding sc sd by (rule bexI[of _ p], rule bexI[of _ q]) (use p q grade in auto)
qed
lemma symbol_mul_grade_le:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pb: "\<And>p. p\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade p\<le>m"
    and qb: "\<And>q. q\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade q\<le>n"
    and u: "u\<in>biv_support (pbw_symbol (op_comp P Q))"
  shows "pair_grade u\<le>m+n"
proof -
  obtain p q where p: "p\<in>biv_support (pbw_symbol P)" and q: "q\<in>biv_support (pbw_symbol Q)"
    and eq: "pair_grade u=pair_grade p+pair_grade q"
    using symbol_mul_grade_decomposition[OF P Q u] by blast
  show ?thesis unfolding eq by (rule add_mono[OF pb[OF p] qb[OF q]])
qed
lemma symbol_mul_top_component:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
  shows "weighted_component rho sigma (m+n) (pbw_symbol (op_comp P Q)) =
    weighted_component rho sigma m (pbw_symbol P)*weighted_component rho sigma n (pbw_symbol Q)"
  by (rule symbol_mul_bound_and_top(2)[OF P Q pos pd qd])
lemma weighted_component_nonzero_of_degree:
  "weighted_degree rho sigma (p::'a::field bivariate)=bot.Value m \<Longrightarrow>
    weighted_component rho sigma m p\<noteq>0"
  by (rule weighted_top_component_nonzero)

end
