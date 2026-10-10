theory Weighted_Newton_Definitions
  imports Partial_Derivatives "Bivariate_Universal"
begin

definition is_direction :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_direction rho sigma \<longleftrightarrow> gcd (nat (abs rho)) (nat (abs sigma)) = 1 \<and> 0 < rho+sigma"
definition in_direction :: "int \<Rightarrow> int \<Rightarrow> 'a::field poly_operator \<Rightarrow> bool" where
  "in_direction rho sigma T \<longleftrightarrow> 1 < card (biv_support (leading_form rho sigma T))"
definition strict_crossing :: "int \<Rightarrow> int \<Rightarrow> 'a::field poly_operator \<Rightarrow> bool" where
  "strict_crossing rho sigma T \<longleftrightarrow> in_direction rho sigma T \<and>
    (\<exists>u\<in>biv_support (leading_form rho sigma T). 0 < pair_grade u) \<and>
    (\<exists>u\<in>biv_support (leading_form rho sigma T). pair_grade u < 0)"
definition total_degree :: "'a::field poly_operator \<Rightarrow> nat" where
  "total_degree T = Max (insert 0 ((\<lambda>u. fst u + snd u) ` biv_support (pbw_symbol T)))"
definition cut_poly :: "int \<Rightarrow> int \<Rightarrow> 'a::field poly_operator \<Rightarrow> 'a poly" where
  "cut_poly rho sigma T = map_poly (\<lambda>p. poly p 1) (leading_form rho sigma T)"
lemma cut_poly_coeff:
  "coeff (cut_poly rho sigma T) j = poly (coeff (leading_form rho sigma T) j) 1"
  by (simp add: cut_poly_def coeff_map_poly)
lemma v_degree_zero [simp]: "v_degree rho sigma 0 = 0"
  by (simp add: v_degree_def)
lemma leading_form_zero [simp]: "leading_form rho sigma 0 = 0"
  by (simp add: leading_form_def)
lemma total_degree_zero [simp]: "total_degree 0 = 0"
  by (simp add: total_degree_def)
lemma cut_poly_zero [simp]: "cut_poly rho sigma 0 = 0"
  by (simp add: cut_poly_def)

lemma constant_polynomial_hom:
  "coefficient_hom (\<lambda>c::'a::field. [:c:] :: 'a poly)"
  by (simp add: coefficient_hom_def one_pCons)
lemma cut_poly_universal_eval:
  "cut_poly rho sigma T = biv_eval (\<lambda>c. [:c:]) 1 [:0,1:] (leading_form rho sigma T)"
proof -
  have eval: "map_poly (\<lambda>q::'a::field poly. poly q 1) = biv_eval (\<lambda>c. [:c:]) 1 [:0,1:]"
    by (rule biv_hom_uniqueness)
       (simp_all add: constant_polynomial_hom coefficient_hom_map_poly coefficient_hom_poly_eval
         biv_monom_def map_poly_monom poly_monom monom_altdef map_poly_pCons)
  show ?thesis by (simp only: cut_poly_def eval)
qed

lemma exponent_total_pair:
  "(\<Sum>b\<in>UNIV. pair_exponent (i,j) b) = i+j"
  by (simp add: UNIV_bool pair_exponent_def add.commute)
lemma total_degree_normal_monomial:
  "total_degree (normal_monomial a b :: 'a::field_char_0 poly_operator) = a+b"
  by (simp add: total_degree_def pbw_symbol_normal_monomial weighted_support_monom)

end
