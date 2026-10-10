theory Horizontal_Crossing_Support
 imports Horizontal_Scalar_Reduction
   "Crossing_Term_Count"
   "Crossing_Scalar_Reduction"
begin

lemma horizontal_base_support_iff:
 "e\<in>biv_support(biv_monom 1 a 0 * biv_univariate_eval(g::complex poly)(biv_monom 1 0 1)) \<longleftrightarrow>
 fst e = a \<and> snd e\<in>sparse_support g"
 by (simp only: biv_support_def horizontal_base_coeff_general sparse_support_def; auto split: if_splits)

lemma horizontal_base_nonpos_of_support_ge:
 assumes support: "\<forall>j\<in>sparse_support(g::complex poly). a\<le>j"
 shows "\<forall>e\<in>biv_support(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)). pair_grade e\<le>0"
proof (intro ballI)
 fix e assume member: "e\<in>biv_support(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1))"
 have coordinates: "fst e = a" and index: "snd e\<in>sparse_support g"
   using iffD1[OF horizontal_base_support_iff member] by blast+
 have bound: "a\<le>snd e" by (rule bspec[OF support index])
 have cast_bound: "int a\<le>int(snd e)" using bound by (simp only: of_nat_le_iff)
 show "pair_grade e\<le>0" using cast_bound by (simp only: pair_grade_def coordinates; arith)
qed

lemma horizontal_base_nonneg_of_support_le:
 assumes support: "\<forall>j\<in>sparse_support(g::complex poly). j\<le>a"
 shows "\<forall>e\<in>biv_support(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)). 0\<le>pair_grade e"
proof (intro ballI)
 fix e assume member: "e\<in>biv_support(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1))"
 have coordinates: "fst e = a" and index: "snd e\<in>sparse_support g"
   using iffD1[OF horizontal_base_support_iff member] by blast+
 have bound: "snd e\<le>a" by (rule bspec[OF support index])
 have cast_bound: "int(snd e)\<le>int a" using bound by (simp only: of_nat_le_iff)
 show "0\<le>pair_grade e" using cast_bound by (simp only: pair_grade_def coordinates; arith)
qed

lemma support_grade_nonneg_pow:
 fixes R::"complex bivariate"
 assumes nonnegative: "\<forall>e\<in>biv_support R. 0\<le>pair_grade e"
 shows "\<forall>e\<in>biv_support(R ^ k). 0\<le>pair_grade e"
proof -
 have bound: "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight ( - 1) 1 e\<le>0"
  using nonnegative by (simp add: pair_weight_def pair_grade_def)
 have power: "\<And>e. e\<in>biv_support(R ^ k) \<Longrightarrow> pair_weight ( - 1) 1 e\<le>int k * 0"
  by (rule corner_support_weight_power[OF bound])
 show ?thesis using power by (simp add: pair_weight_def pair_grade_def)
qed

lemma horizontal_crossing_support_straddles:
 fixes P::"complex poly_operator" and mu::complex and g::"complex poly"
 assumes mu: "mu\<noteq>0"
 and face: "leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)) ^ k"
 and crossing: "strict_crossing 1 0 P"
 shows "(\<exists>j\<in>sparse_support g. j < a) \<and> (\<exists>j\<in>sparse_support g. a < j)"
proof (intro conjI)
 let ?R="biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
 have transport: "biv_support(leading_form 1 0 P) = biv_support(?R ^ k)"
  using mu by (auto simp: face biv_support_def biv_coeff_def)
 show "\<exists>j\<in>sparse_support g. j < a"
 proof (rule ccontr)
  assume "\<not>(\<exists>j\<in>sparse_support g. j < a)"
  then have ge: "\<forall>j\<in>sparse_support g. a\<le>j" by auto
  have base: "\<forall>e\<in>biv_support ?R. pair_grade e\<le>0" by (rule horizontal_base_nonpos_of_support_ge[OF ge])
  have power: "\<forall>e\<in>biv_support(?R ^ k). pair_grade e\<le>0" by (rule support_grade_nonpos_pow[OF base])
  show False using crossing power by (auto simp: strict_crossing_def transport)
 qed
 show "\<exists>j\<in>sparse_support g. a < j"
 proof (rule ccontr)
  assume "\<not>(\<exists>j\<in>sparse_support g. a < j)"
  then have le: "\<forall>j\<in>sparse_support g. j\<le>a" by auto
  have base: "\<forall>e\<in>biv_support ?R. 0\<le>pair_grade e" by (rule horizontal_base_nonneg_of_support_le[OF le])
  have power: "\<forall>e\<in>biv_support(?R ^ k). 0\<le>pair_grade e" by (rule support_grade_nonneg_pow[OF base])
  show False using crossing power by (auto simp: strict_crossing_def transport)
 qed
qed

lemma horizontal_zero_order_le_coeff_index:
 fixes g::"complex poly"
 assumes coefficient: "coeff g j\<noteq>0"
 shows "rootMultiplicity 0 g\<le>j"
proof -
 have g: "g\<noteq>0" using coefficient by auto
 have divides: "[:0,1:] ^ order 0 g dvd g" using order_1[of 0 g] by simp
 obtain q where shape: "g = [:0,1:] ^ order 0 g * q" using divides by (elim dvdE)
 have X: "[:0,1:] ^ order 0 g = monom (1::complex)(order 0 g)" by (simp add: monom_altdef)
 have coefficient_formula: "coeff g j = (if j < order 0 g then 0 else coeff q (j - order 0 g))"
 proof -
   have "coeff g j = coeff ([:0,1:] ^ order 0 g * q) j"
     by (rule arg_cong[where f="\<lambda>p. coeff p j", OF shape])
   also have "... = coeff (monom (1::complex)(order 0 g) * q) j"
     by (simp only: X)
   also have "... = (if j < order 0 g then 0 else coeff q (j - order 0 g))"
     by (simp only: coeff_monom_mult mult_1_left)
   finally show ?thesis .
 qed
 have index: "order 0 g\<le>j"
 proof (rule ccontr)
   assume "\<not>order 0 g\<le>j" then have below: "j < order 0 g" by arith
   have zero: "coeff g j = 0" by (simp only: coefficient_formula below if_True)
   show False using coefficient zero by contradiction
 qed
 show ?thesis by (simp only: rootMultiplicity_eq_order[OF g]; rule index)
qed

lemma horizontal_crossing_order_bounds:
 fixes P::"complex poly_operator" and mu::complex and g::"complex poly"
 assumes mu: "mu\<noteq>0"
 and face: "leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)) ^ k"
 and crossing: "strict_crossing 1 0 P"
 shows "rootMultiplicity 0 g < a \<and> a < degree g"
proof -
 obtain j t where j: "j\<in>sparse_support g" and ja: "j < a" and t: "t\<in>sparse_support g" and at: "a < t"
  using horizontal_crossing_support_straddles[OF mu face crossing] by blast
 have order: "rootMultiplicity 0 g\<le>j" by (rule horizontal_zero_order_le_coeff_index) (use j in simp)
 have degree: "t\<le>degree g" by (rule le_degree) (use t in simp)
 show ?thesis using order degree ja at by arith
qed

lemma horizontal_face_termCount_le_mass:
 fixes P::"complex poly_operator" and mu::complex and g::"complex poly"
 assumes P: "P\<in>weyl_algebra" and mu: "mu\<noteq>0"
 and face: "leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)) ^ k"
 shows "termCount(g ^ k)\<le>weyl_mass P"
 by (rule crossingFace_general_termCount_le_mass[where rho=1 and s=0 and b=0, OF P mu]) (simp, simp add: face)

end
