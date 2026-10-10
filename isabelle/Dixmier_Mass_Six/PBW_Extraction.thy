theory PBW_Extraction
  imports Weyl_Adjunction
begin

text \<open>The prescribed finite-difference extraction is defined on every
polynomial function. In particular it applies to every linear endomorphism;
finite normal-order support is not part of its definition.\<close>

definition coeff_poly :: "'a::field poly_operator \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "coeff_poly T j = smult (inverse (of_nat (fact j)))
    (\<Sum>k\<in>{..<Suc j}. smult ((-1) ^ (j - k) * of_nat (j choose k))
      ([:0, 1:] ^ (j - k) * T ([:0, 1:] ^ k)))"
definition pbw_coeff :: "'a::field poly_operator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "pbw_coeff T i j = coeff (coeff_poly T j) i"

lemma smult_sum_right:
  "smult c (\<Sum>i\<in>A. f i) = (\<Sum>i\<in>A. smult c (f i))"
  by (induction A rule: infinite_finite_induct) (simp_all add: smult_add_right)

lemma coeff_poly_zero_order [simp]: "coeff_poly T 0 = T 1"
  by (simp add: coeff_poly_def)
lemma coeff_poly_zero [simp]: "coeff_poly 0 j = 0"
  by (simp add: coeff_poly_def)
lemma coeff_poly_add:
  "coeff_poly (T + U) j = coeff_poly T j + coeff_poly U j"
  by (simp add: coeff_poly_def algebra_simps smult_add_right sum.distrib)
lemma coeff_poly_smult:
  "coeff_poly (\<lambda>p. smult c (T p)) j = smult c (coeff_poly T j)"
  by (simp add: coeff_poly_def smult_sum_right smult_smult smult_add_right algebra_simps)
lemma pbw_coeff_add:
  "pbw_coeff (T + U) i j = pbw_coeff T i j + pbw_coeff U i j"
  by (simp add: pbw_coeff_def coeff_poly_add)
lemma pbw_coeff_smult:
  "pbw_coeff (\<lambda>p. smult c (T p)) i j = c * pbw_coeff T i j"
  by (simp add: pbw_coeff_def coeff_poly_smult)

end
