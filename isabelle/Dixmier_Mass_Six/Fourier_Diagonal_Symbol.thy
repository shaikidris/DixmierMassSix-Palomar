theory Fourier_Diagonal_Symbol
 imports Fourier_Diagonal_Symbol_Algebra
  "Weyl_Statement_Interfaces"
begin

lemma native_diagonal_component_sum:
 "weighted_component 1 1 N (\<Sum>u\<in>S. f u)=(\<Sum>u\<in>S. weighted_component 1 1 N (f u))"
 by (induction S rule: infinite_finite_induct) (simp_all add: weighted_component_add)
lemma native_support_total_bound:
 assumes "u\<in>biv_support(pbw_symbol P)"
 shows "fst u+snd u\<le>total_degree P"
 unfolding total_degree_def by (rule Max_ge) (use assms in auto)
lemma native_v_degree_diagonal_total:
 "v_degree 1 1 P=int(total_degree P)"
proof (cases "biv_support(pbw_symbol P)={}")
 case True then show ?thesis by (simp add: v_degree_def weighted_degree_def total_degree_def)
next
 case False
 let ?S="biv_support(pbw_symbol P)"
 let ?A="(\<lambda>u. fst u+snd u) ` ?S"
 have finite: "finite ?A" by simp
 have ne: "?A\<noteq>{}" using False by simp
 have total: "total_degree P=Max ?A"
  using finite ne by (simp add: total_degree_def Max_insert)
 obtain u where u: "u\<in>?S" and attained: "fst u+snd u=total_degree P"
  using Max_in[OF finite ne] by (auto simp only: total image_iff)
 have max_value: "Max(pair_weight 1 1 ` ?S)=int(total_degree P)"
 proof (rule Max_eqI)
  show "finite(pair_weight 1 1 ` ?S)" by simp
  show "\<And>w. w\<in>pair_weight 1 1 ` ?S \<Longrightarrow>w\<le>int(total_degree P)"
  proof -
   fix w assume "w\<in>pair_weight 1 1 ` ?S"
   then obtain v where member: "v\<in>?S" and w: "w=pair_weight 1 1 v" by blast
   have bound: "fst v+snd v\<le>total_degree P"
    by (rule native_support_total_bound[OF member])
   have cast: "int(fst v+snd v)\<le>int(total_degree P)" using bound by simp
   show "w\<le>int(total_degree P)" using cast
    by (simp add: w pair_weight_def of_nat_add)
  qed
  show "int(total_degree P)\<in>pair_weight 1 1 ` ?S"
   by (rule image_eqI[OF _ u]) (simp add: pair_weight_def attained[symmetric])
 qed
 show ?thesis using False max_value by (simp add: v_degree_def weighted_degree_def)
qed

lemma antinormal_diagonal_component:
 fixes i j N::nat
 assumes bound: "i+j\<le>N"
 shows "weighted_component 1 1 (int N)
  (pbw_symbol(op_comp (y_op ^^ i)(x_op ^^ j)::complex poly_operator))=
  (if i+j=N then biv_monom 1 j i else 0)"
proof -
 have component_identity: "weighted_component 1 1 (int N)
  (biv_monom (of_nat((i choose k)*nat_desc_factorial j k)::complex)(j-k)(i-k))=
  (if k=0 then (if i+j=N then biv_monom 1 j i else 0) else 0)"
  if k: "k\<le>min j i" for k
 proof (cases "k=0")
  case True then show ?thesis
   by (simp add: weighted_component_monom pair_weight_def add.commute)
 next
  case False
  have ki: "k\<le>i" and kj: "k\<le>j" using k by auto
  have "j-k+(i-k)<N" using bound ki kj False by arith
  then show ?thesis using False
   by (simp add: weighted_component_monom pair_weight_def)
 qed
 have sum_eq: "(\<Sum>k\<le>min j i. weighted_component 1 1 (int N)
  (biv_monom (of_nat((i choose k)*nat_desc_factorial j k)::complex)(j-k)(i-k)))=
  (\<Sum>k\<le>min j i. if k=0 then (if i+j=N then biv_monom 1 j i else 0) else 0)"
 proof (rule sum.cong[OF refl])
  fix k assume "k\<in>{..min j i}"
  then have "k\<le>min j i" by simp
  then show "weighted_component 1 1 (int N)
   (biv_monom (of_nat((i choose k)*nat_desc_factorial j k)::complex)(j-k)(i-k))=
   (if k=0 then (if i+j=N then biv_monom 1 j i else 0) else 0)"
   by (rule component_identity)
 qed
 show ?thesis
  by (simp only: symbol_concreteAntiNormalMonomial native_diagonal_component_sum sum_eq)
    simp
qed

lemma fourier_diagonal_component:
 fixes P::"complex poly_operator" and N::nat
 assumes P: "P\<in>weyl_algebra" and bound: "total_degree P\<le>N"
 shows "weighted_component 1 1 (int N)(pbw_symbol(fourier_alg_hom P))=
  diagonalFourierSymbol(weighted_component 1 1 (int N)(pbw_symbol P))"
proof -
 obtain c::"(nat\<times>nat,complex) poly_mapping" where expansion:
  "finite_normal_sum (Poly_Mapping.keys c)(Poly_Mapping.lookup c)=P"
  using fourier_exists_poly_mapping[OF P] by blast
 have coefficients: "pbw_coeff P (fst u)(snd u)=Poly_Mapping.lookup c u" for u
  by (simp add: expansion[symmetric] pbw_coeff_finite_normal_sum Poly_Mapping.in_keys_iff)
 have support: "biv_support(pbw_symbol P)=Poly_Mapping.keys c"
  by (auto simp: biv_support_def weyl_symbol_coeff[OF P] coefficients Poly_Mapping.in_keys_iff)
 have original: "pbw_symbol P=(\<Sum>u\<in>Poly_Mapping.keys c.
  biv_monom(Poly_Mapping.lookup c u)(fst u)(snd u))"
  using pbw_symbol_finite_normal_sum[of "Poly_Mapping.keys c" "Poly_Mapping.lookup c"]
  by (simp add: expansion)
 have component_identity: "weighted_component 1 1 (int N)
  (smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
   (pbw_symbol(op_comp(y_op ^^ fst u)(x_op ^^ snd u)))))=
  diagonalFourierSymbol(weighted_component 1 1 (int N)
   (biv_monom(Poly_Mapping.lookup c u)(fst u)(snd u)))"
  if u: "u\<in>Poly_Mapping.keys c" for u
 proof -
  have raw: "u\<in>biv_support(pbw_symbol P)" using u by(simp only: support)
  have deg: "fst u+snd u\<le>N"
   using native_support_total_bound[OF raw] bound by arith
  have original_component: "weighted_component 1 1 (int N)
   (biv_monom(Poly_Mapping.lookup c u)(fst u)(snd u))=
   (if fst u+snd u=N then biv_monom(Poly_Mapping.lookup c u)(fst u)(snd u) else 0)"
   by (simp only: weighted_component_monom pair_weight_def fst_conv snd_conv)
     (simp add: of_nat_add)
  have zero_image: "diagonalFourierSymbol 0=0"
   using diagonalFourierSymbol_hom unfolding coefficient_hom_def by blast
  show ?thesis
   by (simp only: weighted_component_smult antinormal_diagonal_component[OF deg]
       original_component if_distrib diagonalFourierSymbol_monomial zero_image)
     (simp add: biv_monom_def smult_monom add.commute)
 qed
 show ?thesis
  by (simp only: symbol_fourierAlgHom_eq_sum[OF P expansion]
    native_diagonal_component_sum original diagonalFourierSymbol_sum;
    rule sum.cong; simp only: component_identity)
qed

lemma fourier_diagonal_leadingForm:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "leading_form 1 1(fourier_alg_hom P)=diagonalFourierSymbol(leading_form 1 1 P)"
 using fourier_diagonal_component[OF P order_refl]
 by (simp add: leading_form_def native_v_degree_diagonal_total totalDeg_fourier_eq[OF P])
lemma counterexample_fourier_diagonal_leadingForm:
 fixes P Q::"complex poly_operator"
 assumes "is_counterexample_pair P Q"
 shows "leading_form 1 1(fourier_alg_hom P)=diagonalFourierSymbol(leading_form 1 1 P)"
 by (rule fourier_diagonal_leadingForm) (use assms in \<open>simp add: is_counterexample_pair_def\<close>)
lemma cut_fourier_diagonal_evaluation:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "cut_poly 1 1(fourier_alg_hom P)=poly(leading_form 1 1 P)([:-1:]::complex poly)"
 by (simp only: cut_poly_def fourier_diagonal_leadingForm[OF P]
   diagonalFourierSymbol_evaluation)

end
