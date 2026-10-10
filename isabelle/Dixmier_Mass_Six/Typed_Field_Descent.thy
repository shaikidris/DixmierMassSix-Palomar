theory Typed_Field_Descent
  imports "HOL.Vector_Spaces"
begin

text \<open>This is the whole-type field-extension result F0. It does not instantiate
its scalar type with a value-level subfield carrier.\<close>

locale dixmier_field_embedding =
  fixes i :: "'k::field \<Rightarrow> 'l::field"
  assumes map_one: "i 1 = 1"
    and map_add: "i (a + b) = i a + i b"
    and map_mult: "i (a * b) = i a * i b"
    and injective: "inj i"
begin

interpretation source: vector_space "(*) :: 'k \<Rightarrow> 'k \<Rightarrow> 'k"
  by standard (simp_all add: algebra_simps)

interpretation target: vector_space "\<lambda>a z. i a * z"
  by standard (simp_all add: map_one map_add map_mult algebra_simps)

interpretation pair: vector_space_pair "(*) :: 'k \<Rightarrow> 'k \<Rightarrow> 'k"
    "\<lambda>a z. i a * z"
  by (rule vector_space_pair.intro[OF source.vector_space_axioms target.vector_space_axioms])

lemma embedding_linear:
  "Vector_Spaces.linear (*) (\<lambda>a z. i a * z) i"
  unfolding Vector_Spaces.linear_iff
  using source.vector_space_axioms target.vector_space_axioms map_add map_mult
  by blast

theorem exists_field_extension_retraction:
  "\<exists>r :: 'l \<Rightarrow> 'k.
    Vector_Spaces.linear (\<lambda>a z. i a * z) (*) r \<and> (\<forall>a. r (i a) = a)"
proof -
  obtain r where r: "Vector_Spaces.linear (\<lambda>a z. i a * z) (*) r" "r \<circ> i = id"
    using pair.linear_injective_left_inverse[OF embedding_linear injective] by blast
  have "\<forall>a. r (i a) = a"
    using r(2) by (simp add: fun_eq_iff)
  then show ?thesis using r(1) by blast
qed

theorem finite_linear_system_descends:
  fixes J :: "'j set" and A :: "'m \<Rightarrow> 'j \<Rightarrow> 'k" and b :: "'m \<Rightarrow> 'k"
  assumes finite_J: "finite J"
    and solution: "\<exists>x :: 'j \<Rightarrow> 'l. \<forall>m.
      (\<Sum>j\<in>J. i (A m j) * x j) = i (b m)"
  shows "\<exists>y :: 'j \<Rightarrow> 'k. \<forall>m. (\<Sum>j\<in>J. A m j * y j) = b m"
proof -
  obtain r where rlin: "Vector_Spaces.linear (\<lambda>a z. i a * z) (*) r"
    and retract: "\<forall>a. r (i a) = a"
    using exists_field_extension_retraction by blast
  interpret r: Vector_Spaces.linear "\<lambda>a z. i a * z" "(*) :: 'k \<Rightarrow> 'k \<Rightarrow> 'k" r
    by (rule rlin)
  obtain x where x: "\<forall>m. (\<Sum>j\<in>J. i (A m j) * x j) = i (b m)"
    using solution by blast
  show ?thesis
  proof (intro exI[of _ "\<lambda>j. r (x j)"] allI)
    fix m
    have "r (\<Sum>j\<in>J. i (A m j) * x j) = r (i (b m))"
      using x by simp
    then show "(\<Sum>j\<in>J. A m j * r (x j)) = b m"
      by (simp only: r.sum r.scale retract)
  qed
qed

corollary finite_type_linear_system_descends:
  fixes A :: "'m \<Rightarrow> 'j::finite \<Rightarrow> 'k" and b :: "'m \<Rightarrow> 'k"
  assumes "\<exists>x :: 'j \<Rightarrow> 'l. \<forall>m.
      (\<Sum>j\<in>UNIV. i (A m j) * x j) = i (b m)"
  shows "\<exists>y :: 'j \<Rightarrow> 'k. \<forall>m. (\<Sum>j\<in>UNIV. A m j * y j) = b m"
  using finite_linear_system_descends[OF finite_UNIV assms] .

end

end
