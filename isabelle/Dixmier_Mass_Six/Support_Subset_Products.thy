theory Support_Subset_Products
  imports "Support_Test_Polynomial"
begin

lemma sum_testPoly_sdiff:
  fixes w :: "nat \<Rightarrow> 'a::field"
  assumes fin: "finite N" and sub: "U \<subseteq> N"
  shows "(\<Sum>m\<in>N. w m * poly (testPoly (N-U)) (of_nat m)) =
    (\<Sum>m\<in>U. w m * poly (testPoly (N-U)) (of_nat m))"
  by (rule sum.mono_neutral_right[OF fin sub])
    (use fin in \<open>auto simp: eval_testPoly_eq_zero\<close>)

lemma prod_erase_eq_eval_testPoly_mul:
  fixes N U :: "nat set"
  assumes fin: "finite N" and sub: "U \<subseteq> N" and kin: "k \<in> U"
  shows "(\<Prod>m\<in>N-{k}. (of_nat k - of_nat m :: 'a::field)) =
    poly (testPoly (N-U)) (of_nat k) *
      (\<Prod>m\<in>U-{k}. (of_nat k - of_nat m))"
proof -
  have finiteU: "finite U" using sub fin by (rule finite_subset)
  have eq: "N-{k} = (N-U) \<union> (U-{k})" using sub kin by blast
  have disj: "(N-U) \<inter> (U-{k}) = {}" by blast
  show ?thesis
    unfolding eq
    using fin finiteU disj
    by (simp add: prod.union_disjoint eval_testPoly)
qed

end
