theory Exact_Grade_Projection
  imports "Weyl_Grade_Convolution" "HOL-Library.Poly_Mapping"
begin

lemma symbol_mul_grade_eq:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pg: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u=g"
    and qg: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u=h"
  shows "u\<in>biv_support (pbw_symbol (op_comp P Q)) \<Longrightarrow> pair_grade u=g+h"
proof -
  assume u: "u\<in>biv_support (pbw_symbol (op_comp P Q))"
  obtain p q where p: "p\<in>biv_support (pbw_symbol P)" and q: "q\<in>biv_support (pbw_symbol Q)"
    and eq: "pair_grade u=pair_grade p+pair_grade q"
    using symbol_mul_grade_decomposition[OF P Q u] by blast
  show ?thesis using eq pg[OF p] qg[OF q] by simp
qed

lemma symbol_sub_grade_eq:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pg: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u=g"
    and qg: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u=g"
  shows "u\<in>biv_support (pbw_symbol (P-Q)) \<Longrightarrow> pair_grade u=g"
proof -
  assume u: "u\<in>biv_support (pbw_symbol (P-Q))"
  have diff: "P-Q\<in>weyl_algebra"
    using P Q unfolding weyl_algebra_def by (rule op_adjoin.diff)
  have nz: "pbw_coeff P (fst u) (snd u)-pbw_coeff Q (fst u) (snd u)\<noteq>0"
    using u by (simp add: weyl_symbol_support[OF diff] pbw_pair_support_def pbw_coeff_diff)
  have "u\<in>biv_support (pbw_symbol P) \<or> u\<in>biv_support (pbw_symbol Q)"
    using nz by (auto simp: weyl_symbol_support[OF P] weyl_symbol_support[OF Q] pbw_pair_support_def)
  then show ?thesis using pg qg by blast
qed

definition grade_filtered_coeffs :: "(nat\<times>nat,complex) poly_mapping \<Rightarrow> int \<Rightarrow> (nat\<times>nat,complex) poly_mapping" where
  "grade_filtered_coeffs c g = Poly_Mapping.Abs_poly_mapping
    (\<lambda>u. if pair_grade u=g then Poly_Mapping.lookup c u else 0)"

lemma grade_filtered_coeffs_lookup:
  "Poly_Mapping.lookup (grade_filtered_coeffs c g) u =
    (if pair_grade u=g then Poly_Mapping.lookup c u else 0)"
proof -
  have sub: "{u. (if pair_grade u=g then Poly_Mapping.lookup c u else 0)\<noteq>0}
    \<subseteq> Poly_Mapping.keys c" by (auto simp: Poly_Mapping.in_keys_iff)
  have fin: "finite {u. (if pair_grade u=g then Poly_Mapping.lookup c u else 0)\<noteq>0}"
    by (rule finite_subset[OF sub Poly_Mapping.finite_keys])
  show ?thesis unfolding grade_filtered_coeffs_def using Poly_Mapping.lookup_Abs_poly_mapping[OF fin] by simp
qed

definition grade_filtered_sum :: "(nat\<times>nat,complex) poly_mapping \<Rightarrow> int \<Rightarrow> complex poly_operator" where
  "grade_filtered_sum c g = finite_normal_sum (Poly_Mapping.keys (grade_filtered_coeffs c g))
    (Poly_Mapping.lookup (grade_filtered_coeffs c g))"
lemma grade_filtered_sum_mem:
  "grade_filtered_sum c g\<in>weyl_algebra"
  unfolding grade_filtered_sum_def by (rule finite_normal_sum_in_weyl) simp

definition grade_filtered_element :: "(nat\<times>nat,complex) poly_mapping \<Rightarrow> int \<Rightarrow> complex poly_operator" where
  "grade_filtered_element c g = grade_filtered_sum c g"
lemma grade_filtered_element_mem:
  "grade_filtered_element c g\<in>weyl_algebra"
  unfolding grade_filtered_element_def by (rule grade_filtered_sum_mem)
lemma grade_filtered_element_coeff:
  "pbw_coeff (grade_filtered_element c g) i j =
    (if int i-int j=g then Poly_Mapping.lookup c (i,j) else 0)"
  unfolding grade_filtered_element_def grade_filtered_sum_def
  by (simp add: pbw_coeff_finite_normal_sum Poly_Mapping.in_keys_iff grade_filtered_coeffs_lookup pair_grade_def)
lemma grade_filtered_element_has_grade:
  "u\<in>biv_support (pbw_symbol (grade_filtered_element c g)) \<Longrightarrow> pair_grade u=g"
  by (auto simp: weyl_symbol_support[OF grade_filtered_element_mem] pbw_pair_support_def
      grade_filtered_element_coeff pair_grade_def split: if_splits)

lemma exists_exact_grade_projection:
  fixes T :: "complex poly_operator"
  assumes T: "T\<in>weyl_algebra"
  shows "\<exists>S\<in>weyl_algebra.
    (\<forall>u\<in>biv_support (pbw_symbol S). pair_grade u=g) \<and>
    (\<forall>i j. pbw_coeff S i j=(if int i-int j=g then pbw_coeff T i j else 0))"
proof -
  let ?c = "Poly_Mapping.Abs_poly_mapping (\<lambda>u. pbw_coeff T (fst u) (snd u))"
  have lk: "Poly_Mapping.lookup ?c=(\<lambda>u. pbw_coeff T (fst u) (snd u))"
    by (rule Poly_Mapping.lookup_Abs_poly_mapping[OF weyl_pbw_finite_support[OF T]])
  show ?thesis
    by (rule bexI[of _ "grade_filtered_element ?c g"])
      (auto simp: grade_filtered_element_coeff lk intro: grade_filtered_element_has_grade grade_filtered_element_mem)
qed

lemma grade_projection_remainder_le:
  fixes T S :: "complex poly_operator"
  assumes T: "T\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
    and upper: "\<And>u. u\<in>biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u\<le>g"
    and coeff: "\<And>i j. pbw_coeff S i j=(if int i-int j=g then pbw_coeff T i j else 0)"
  shows "u\<in>biv_support (pbw_symbol (T-S)) \<Longrightarrow> pair_grade u\<le>g-1"
proof -
  assume u: "u\<in>biv_support (pbw_symbol (T-S))"
  have diff: "T-S\<in>weyl_algebra"
    using T S unfolding weyl_algebra_def by (rule op_adjoin.diff)
  have nz: "pbw_coeff T (fst u) (snd u)-pbw_coeff S (fst u) (snd u)\<noteq>0"
    using u by (simp add: weyl_symbol_support[OF diff] pbw_pair_support_def pbw_coeff_diff)
  have ne: "pair_grade u\<noteq>g" and tnz: "pbw_coeff T (fst u) (snd u)\<noteq>0"
    using nz by (auto simp: coeff pair_grade_def split: if_splits)
  have mem: "u\<in>biv_support (pbw_symbol T)"
    using tnz by (simp add: weyl_symbol_support[OF T] pbw_pair_support_def)
  show ?thesis using upper[OF mem] ne by linarith
qed
end
