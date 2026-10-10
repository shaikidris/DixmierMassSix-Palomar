theory Degree_Minimal_Pair
  imports "Weyl_Statement_Interfaces"
begin

text \<open>Exact GGVMinimalPair.lean source architecture: natural well-ordering
of the degree gcd and transfer to every counterexample pair. Complex operators
are constrained only by the existing \<^verbatim>\<open>is_counterexample_pair\<close> predicate; no mate
order bound is introduced. Source 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

definition is_degree_minimal_counterexample_pair ::
  "complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow> bool" where
  "is_degree_minimal_counterexample_pair P Q \<longleftrightarrow>
    is_counterexample_pair P Q \<and>
    (\<forall>R S. is_counterexample_pair R S \<longrightarrow>
      gcd (total_degree P) (total_degree Q) \<le>
      gcd (total_degree R) (total_degree S))"

lemma exists_degreeMinimalCounterexamplePair:
  assumes pair: "is_counterexample_pair P Q"
  shows "\<exists>R S. is_degree_minimal_counterexample_pair R S"
proof -
  let ?values = "\<lambda>d::nat. \<exists>R S::complex poly_operator.
    is_counterexample_pair R S \<and> d=gcd (total_degree R) (total_degree S)"
  have inhabited: "\<exists>d. ?values d" using pair by blast
  have attained: "?values (Least ?values)" by (rule LeastI_ex[OF inhabited])
  obtain R S where counterexample: "is_counterexample_pair R S"
    and degree: "Least ?values=gcd (total_degree R) (total_degree S)"
    using attained by blast
  have minimal: "gcd (total_degree R) (total_degree S) \<le>
    gcd (total_degree T) (total_degree U)" if other: "is_counterexample_pair T U" for T U
  proof -
    have member: "?values (gcd (total_degree T) (total_degree U))" using other by blast
    have "Least ?values \<le> gcd (total_degree T) (total_degree U)"
      by (rule Least_le[where P="?values", OF member])
    then show ?thesis by (simp only: degree)
  qed
  show ?thesis using counterexample minimal
    unfolding is_degree_minimal_counterexample_pair_def by blast
qed

lemma degreeBound_of_minimalPair_bound:
  assumes minimal_bound: "\<And>P Q. is_degree_minimal_counterexample_pair P Q \<Longrightarrow>
    15<gcd (total_degree P) (total_degree Q)"
    and pair: "is_counterexample_pair P Q"
  shows "15<gcd (total_degree P) (total_degree Q)"
proof -
  obtain R S where minimal: "is_degree_minimal_counterexample_pair R S"
    using exists_degreeMinimalCounterexamplePair[OF pair] by blast
  have lower: "15<gcd (total_degree R) (total_degree S)"
    by (rule minimal_bound[OF minimal])
  have compare: "gcd (total_degree R) (total_degree S) \<le>
      gcd (total_degree P) (total_degree Q)"
    using minimal pair unfolding is_degree_minimal_counterexample_pair_def by blast
  show ?thesis by (rule less_le_trans[OF lower compare])
qed

end
