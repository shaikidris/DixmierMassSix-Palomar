theory Weyl_Symbol_Product
  imports "PBW_Contraction_Polynomials"
begin

lemma weyl_sum_closed:
  assumes "\<And>i. i\<in>S \<Longrightarrow> f i \<in> weyl_algebra"
  shows "(\<Sum>i\<in>S. f i) \<in> weyl_algebra"
  using assms unfolding weyl_algebra_def by (rule op_adjoin_sum)
lemma weyl_scalar_closed:
  "T\<in>weyl_algebra \<Longrightarrow> (\<lambda>p. smult c (T p)) \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_smult)
lemma weyl_composition_closed:
  "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> op_comp T U \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.comp)
lemma weyl_symbol_sum:
  assumes fin: "finite S"
    and mem: "\<And>i. i\<in>S \<Longrightarrow> f i \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "pbw_symbol (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. pbw_symbol (f i))"
  using fin mem
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp only: sum.empty pbw_symbol_zero)
next
  case (insert i S)
  have fi: "f i \<in> weyl_algebra" by (rule insert.prems) simp
  have fs: "\<And>j. j\<in>S \<Longrightarrow> f j \<in> weyl_algebra" by (rule insert.prems) simp
  have sum: "(\<Sum>j\<in>S. f j) \<in> weyl_algebra" by (rule weyl_sum_closed[OF fs])
  show ?case using insert.hyps insert.IH[OF fs]
    by (simp only: sum.insert insert.hyps weyl_symbol_add[OF fi sum])
qed
lemma biv_smult_monom:
  "smult [:a:] (biv_monom b i j) = biv_monom (a*b) i j"
  by (rule biv_eqI) simp
lemma symbol_composition_finite_coordinates:
  assumes fs: "finite S" and ft: "finite T"
  shows "pbw_symbol (op_comp (finite_normal_sum S c) (finite_normal_sum T d) :: 'a::field_char_0 poly_operator) =
    pbw_product_polynomial S T c d"
  unfolding finite_normal_sum_mul[OF fs ft] pbw_product_polynomial_def contraction_term_def
  by (simp add: weyl_symbol_sum fs ft weyl_sum_closed weyl_scalar_closed
      normal_monomial_in_weyl weyl_symbol_smult pbw_symbol_normal_monomial biv_smult_monom)
lemma symbol_finite_coordinates_polynomial:
  "finite S \<Longrightarrow> pbw_symbol (finite_normal_sum S c :: 'a::field_char_0 poly_operator) = coordinate_polynomial S c"
  by (simp only: pbw_symbol_finite_normal_sum coordinate_polynomial_def)

lemma symbol_commutator_top_component:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)"
    and Q: "Q\<in>weyl_algebra" and pos: "0 < rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P) = bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q) = bot.Value n"
  shows "weighted_component rho sigma (m+n-(rho+sigma))
      (pbw_symbol (op_comp P Q - op_comp Q P)) =
    biv_poisson (weighted_component rho sigma m (pbw_symbol P))
      (weighted_component rho sigma n (pbw_symbol Q))"
proof -
  obtain c where fc: "finite {u. c u\<noteq>0}" and pc: "finite_normal_sum {u. c u\<noteq>0} c=P"
    and sc: "biv_support (pbw_symbol P)={u. c u\<noteq>0}"
    using symbol_support_finite_expansion[OF P] by blast
  obtain d where fd: "finite {u. d u\<noteq>0}" and qdrep: "finite_normal_sum {u. d u\<noteq>0} d=Q"
    and sd: "biv_support (pbw_symbol Q)={u. d u\<noteq>0}"
    using symbol_support_finite_expansion[OF Q] by blast
  let ?S = "{u. c u\<noteq>0}"
  let ?T = "{u. d u\<noteq>0}"
  have cb: "\<And>u. u\<in>?S \<Longrightarrow> pair_weight rho sigma u \<le> m"
    by (rule weighted_degree_support_bound[OF pd]) (simp only: sc)
  have db: "\<And>u. u\<in>?T \<Longrightarrow> pair_weight rho sigma u \<le> n"
    by (rule weighted_degree_support_bound[OF qd]) (simp only: sd)
  have sp: "pbw_symbol P = coordinate_polynomial ?S c"
    using symbol_finite_coordinates_polynomial[OF fc, of c] by (simp only: pc)
  have sq: "pbw_symbol Q = coordinate_polynomial ?T d"
    using symbol_finite_coordinates_polynomial[OF fd, of d] by (simp only: qdrep)
  have pq: "pbw_symbol (op_comp P Q) = pbw_product_polynomial ?S ?T c d"
    using symbol_composition_finite_coordinates[OF fc fd, of c d] by (simp only: pc qdrep)
  have qp: "pbw_symbol (op_comp Q P) = pbw_product_polynomial ?T ?S d c"
    using symbol_composition_finite_coordinates[OF fd fc, of d c] by (simp only: pc qdrep)
  show ?thesis
    by (simp only: weyl_symbol_sub[OF weyl_composition_closed[OF P Q] weyl_composition_closed[OF Q P]] pq qp sp sq;
        rule pbw_product_commutator_top[OF pos cb db])
qed

lemma pbw_product_top_component:
  assumes pos: "0<rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p \<le> m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q \<le> n"
  shows "weighted_component rho sigma (m+n) (pbw_product_polynomial S T c d) =
    weighted_component rho sigma m (coordinate_polynomial S c) *
    weighted_component rho sigma n (coordinate_polynomial T d)"
proof -
  have pair_top: "weighted_component rho sigma (m+n)
      (\<Sum>k\<le>min (fst q) (snd p). contraction_term c d p q k) =
    weighted_component rho sigma (m+n)
      (biv_monom (c p) (fst p) (snd p) * biv_monom (d q) (fst q) (snd q))"
    if p: "p\<in>S" and q: "q\<in>T" for p q
  proof -
    let ?v = "weighted_component rho sigma (m+n)
      (biv_monom (c p) (fst p) (snd p) * biv_monom (d q) (fst q) (snd q))"
    have term_eq: "weighted_component rho sigma (m+n) (contraction_term c d p q k) =
      (if k=0 then ?v else 0)" if k: "k\<le>min (fst q) (snd p)" for k
    proof (cases "k=0")
      case True
      then show ?thesis by (simp only: True contraction_term_zero if_True)
    next
      case False
      have kp: "0<k" using False by arith
      have less: "pair_weight rho sigma (fst p+fst q-k,snd p+snd q-k) <
        pair_weight rho sigma (fst p+fst q,snd p+snd q)"
        by (rule normal_contraction_weight_lt[OF pos k kp])
      have bound: "pair_weight rho sigma (fst p+fst q,snd p+snd q) \<le> m+n"
        using cb[OF p] db[OF q] by (simp add: pair_weight_def algebra_simps)
      have ne: "pair_weight rho sigma (fst p+fst q-k,snd p+snd q-k) \<noteq> m+n"
        using less bound by arith
      show ?thesis by (simp only: contraction_term_def weighted_component_monom ne False if_False)
    qed
    have sums: "(\<Sum>k\<le>min (fst q) (snd p). weighted_component rho sigma (m+n) (contraction_term c d p q k)) =
      (\<Sum>k\<le>min (fst q) (snd p). if k=0 then ?v else 0)"
      by (rule sum.cong) (simp_all add: term_eq)
    show ?thesis by (simp only: weighted_component_sum sums) simp
  qed
  have poly_top: "weighted_component rho sigma (m+n) (pbw_product_polynomial S T c d) =
      weighted_component rho sigma (m+n) (coordinate_polynomial S c * coordinate_polynomial T d)"
  proof -
    have eq: "(\<Sum>p\<in>S. \<Sum>q\<in>T. weighted_component rho sigma (m+n)
      (\<Sum>k\<le>min (fst q) (snd p). contraction_term c d p q k)) =
      (\<Sum>p\<in>S. \<Sum>q\<in>T. weighted_component rho sigma (m+n)
        (biv_monom (c p) (fst p) (snd p) * biv_monom (d q) (fst q) (snd q)))"
      by (intro sum.cong refl; rule pair_top; assumption)
    show ?thesis using eq
      by (simp only: pbw_product_polynomial_def coordinate_polynomial_def sum_distrib_right;
          simp only: sum_distrib_left weighted_component_sum)
  qed
  have cp: "\<And>u. u\<in>biv_support (coordinate_polynomial S c) \<Longrightarrow> pair_weight rho sigma u \<le> m"
    by (rule coordinate_polynomial_support_bound[OF cb])
  have dp: "\<And>u. u\<in>biv_support (coordinate_polynomial T d) \<Longrightarrow> pair_weight rho sigma u \<le> n"
    by (rule coordinate_polynomial_support_bound[OF db])
  show ?thesis by (simp only: poly_top weighted_component_product_of_bounds[OF cp dp])
qed

end
