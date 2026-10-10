theory Finite_Weyl_Span_Descent
  imports "Concrete_Field_Base_Change"
begin

context dixmier_char_zero_embedding
begin

theorem finite_weyl_span_descends:
  fixes J :: "'j set" and v :: "'j \<Rightarrow> 'k poly_operator" and T :: "'k poly_operator"
  assumes finite_J: "finite J"
    and vectors: "\<And>j. j \<in> J \<Longrightarrow> v j \<in> weyl_algebra"
    and target: "T \<in> weyl_algebra"
    and solution: "\<exists>a :: 'j \<Rightarrow> 'l.
      (\<Sum>j\<in>J. (\<lambda>p. smult (a j) (concrete_base_change i (v j) p))) = concrete_base_change i T"
  shows "\<exists>b :: 'j \<Rightarrow> 'k. (\<Sum>j\<in>J. (\<lambda>p. smult (b j) (v j p))) = T"
proof -
  obtain r where rlin: "Vector_Spaces.linear (\<lambda>a z. i a * z) (*) r"
    and rfix: "\<forall>a. r (i a) = a"
    using exists_field_extension_retraction by blast
  interpret rlin: Vector_Spaces.linear "\<lambda>a z. i a * z" "(*) :: 'k \<Rightarrow> 'k \<Rightarrow> 'k" r
    by (rule rlin)
  obtain a where equality:
    "(\<Sum>j\<in>J. (\<lambda>p. smult (a j) (concrete_base_change i (v j) p))) = concrete_base_change i T"
    using solution by blast
  let ?S = "\<Sum>j\<in>J. (\<lambda>p. smult (r (a j)) (v j p))"
  have source_sum: "?S \<in> weyl_algebra"
    by (intro bc_weyl_sum bc_weyl_smult vectors)
  have result: "?S = T"
  proof (rule weyl_pbw_injective[OF source_sum target])
    fix u w
    have coordinates: "(\<Sum>j\<in>J. a j * i (pbw_coeff (v j) u w)) = i (pbw_coeff T u w)"
      using arg_cong[OF equality, of "\<lambda>V. pbw_coeff V u w"]
      by (simp add: bc_pbw_coeff_sum pbw_coeff_smult
          pbw_coeff_concrete_base_change[OF vectors] pbw_coeff_concrete_base_change[OF target])
    have retracted_term: "r (a j * i (pbw_coeff (v j) u w)) = r (a j) * pbw_coeff (v j) u w" for j
    proof -
      have "r (a j * i (pbw_coeff (v j) u w)) = r (i (pbw_coeff (v j) u w) * a j)"
        by (simp only: mult.commute)
      also have "\<dots> = pbw_coeff (v j) u w * r (a j)" by (rule rlin.scale)
      also have "\<dots> = r (a j) * pbw_coeff (v j) u w" by (rule mult.commute)
      finally show ?thesis .
    qed
    have "(\<Sum>j\<in>J. r (a j) * pbw_coeff (v j) u w) = pbw_coeff T u w"
      using arg_cong[OF coordinates, of r]
      by (simp only: rlin.sum retracted_term rfix)
    then show "pbw_coeff ?S u w = pbw_coeff T u w"
      by (simp only: bc_pbw_coeff_sum pbw_coeff_smult)
  qed
  show ?thesis by (rule exI[of _ "\<lambda>j. r (a j)"]) (rule result)
qed

corollary finite_type_weyl_span_descends:
  fixes v :: "'j::finite \<Rightarrow> 'k poly_operator" and T :: "'k poly_operator"
  assumes vectors: "\<And>j. v j \<in> weyl_algebra"
    and target: "T \<in> weyl_algebra"
    and solution: "\<exists>a :: 'j \<Rightarrow> 'l.
      (\<Sum>j\<in>UNIV. (\<lambda>p. smult (a j) (concrete_base_change i (v j) p))) = concrete_base_change i T"
  shows "\<exists>b :: 'j \<Rightarrow> 'k. (\<Sum>j\<in>UNIV. (\<lambda>p. smult (b j) (v j p))) = T"
  by (rule finite_weyl_span_descends[OF finite_UNIV _ target solution]) (rule vectors)

lemma empty_family_descent_control:
  assumes "T \<in> weyl_algebra" "concrete_base_change i T = 0"
  shows "T = 0"
proof -
  have sol: "\<exists>a :: nat \<Rightarrow> 'l.
    (\<Sum>j\<in>{}. (\<lambda>p. smult (a j) (concrete_base_change i (0 :: 'k poly_operator) p))) = concrete_base_change i T"
    using assms(2) by simp
  obtain b :: "nat \<Rightarrow> 'k" where "(\<Sum>j\<in>{}. (\<lambda>p. smult (b j) ((0 :: 'k poly_operator) p))) = T"
    using finite_weyl_span_descends[OF finite.emptyI _ assms(1) sol] by auto
  then show ?thesis by simp
qed

end
end
