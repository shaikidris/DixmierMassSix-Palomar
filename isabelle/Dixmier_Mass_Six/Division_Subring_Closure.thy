theory Division_Subring_Closure
  imports "PBW_Finite_Coordinates" "HOL-Library.Countable_Set"
begin

text \<open>The generic carrier is a sub-division ring. No commutativity is
assumed: this matches Mathlib Subfield over DivisionRing, whereas the
HOL-Algebra subfield locale would impose commutativity.\<close>

definition division_subring_on :: "'a::division_ring set \<Rightarrow> bool" where
  "division_subring_on E \<longleftrightarrow>
    0 \<in> E \<and> 1 \<in> E \<and>
    (\<forall>x\<in>E. -x \<in> E) \<and> (\<forall>x\<in>E. inverse x \<in> E) \<and>
    (\<forall>x\<in>E. \<forall>y\<in>E. x+y \<in> E \<and> x*y \<in> E)"

fun division_closure_stage :: "'a::division_ring set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "division_closure_stage S 0 = insert 0 (insert 1 S)"
| "division_closure_stage S (Suc n) = division_closure_stage S n \<union>
    uminus ` division_closure_stage S n \<union>
    inverse ` division_closure_stage S n \<union>
    (\<lambda>p. fst p + snd p) ` (division_closure_stage S n \<times> division_closure_stage S n) \<union>
    (\<lambda>p. fst p * snd p) ` (division_closure_stage S n \<times> division_closure_stage S n)"

definition division_closure :: "'a::division_ring set \<Rightarrow> 'a set" where
  "division_closure S = (\<Union>n. division_closure_stage S n)"

lemma division_closure_stage_step:
  "division_closure_stage S n \<subseteq> division_closure_stage S (Suc n)"
  by auto
lemma division_closure_stage_monotone:
  "mono (division_closure_stage S)"
  unfolding mono_iff_le_Suc by (intro allI division_closure_stage_step)
lemma division_closure_stage_mono:
  "n \<le> m \<Longrightarrow> division_closure_stage S n \<subseteq> division_closure_stage S m"
  by (rule monoD[OF division_closure_stage_monotone])
lemma division_closure_stage_member:
  "x \<in> division_closure_stage S n \<Longrightarrow> x \<in> division_closure S"
  unfolding division_closure_def by blast
lemma division_closure_generator:
  assumes "x \<in> S"
  shows "x \<in> division_closure S"
proof -
  have "x \<in> division_closure_stage S 0" using assms by simp
  then show ?thesis by (rule division_closure_stage_member)
qed
lemma division_closure_contains: "S \<subseteq> division_closure S"
  by (auto intro: division_closure_generator)
lemma division_closure_zero: "0 \<in> division_closure S"
proof -
  have "0 \<in> division_closure_stage S 0" by simp
  then show ?thesis by (rule division_closure_stage_member)
qed
lemma division_closure_one: "1 \<in> division_closure S"
proof -
  have "1 \<in> division_closure_stage S 0" by simp
  then show ?thesis by (rule division_closure_stage_member)
qed
lemma division_closure_neg:
  assumes "x \<in> division_closure S"
  shows "-x \<in> division_closure S"
proof -
  obtain n where x: "x \<in> division_closure_stage S n" using assms unfolding division_closure_def by blast
  have "-x \<in> division_closure_stage S (Suc n)" using x by auto
  then show ?thesis by (rule division_closure_stage_member)
qed
lemma division_closure_inverse:
  assumes "x \<in> division_closure S"
  shows "inverse x \<in> division_closure S"
proof -
  obtain n where x: "x \<in> division_closure_stage S n" using assms unfolding division_closure_def by blast
  have "inverse x \<in> division_closure_stage S (Suc n)" using x by auto
  then show ?thesis by (rule division_closure_stage_member)
qed
lemma division_closure_binary:
  assumes "x \<in> division_closure S" "y \<in> division_closure S"
  shows "x+y \<in> division_closure S \<and> x*y \<in> division_closure S"
proof -
  obtain n m where x: "x \<in> division_closure_stage S n" and y: "y \<in> division_closure_stage S m"
    using assms unfolding division_closure_def by blast
  have xn: "x \<in> division_closure_stage S (max n m)"
    using division_closure_stage_mono[where S=S and n=n and m="max n m"] x by auto
  have yn: "y \<in> division_closure_stage S (max n m)"
    using division_closure_stage_mono[where S=S and n=m and m="max n m"] y by auto
  have pair: "(x,y) \<in> division_closure_stage S (max n m) \<times> division_closure_stage S (max n m)"
    using xn yn by simp
  have add_image: "x+y \<in> (\<lambda>p. fst p + snd p) `
      (division_closure_stage S (max n m) \<times> division_closure_stage S (max n m))"
    using imageI[OF pair, of "\<lambda>p. fst p + snd p"] by simp
  have mult_image: "x*y \<in> (\<lambda>p. fst p * snd p) `
      (division_closure_stage S (max n m) \<times> division_closure_stage S (max n m))"
    using imageI[OF pair, of "\<lambda>p. fst p * snd p"] by simp
  have add_stage: "x+y \<in> division_closure_stage S (Suc (max n m))" using add_image by simp
  have mult_stage: "x*y \<in> division_closure_stage S (Suc (max n m))" using mult_image by simp
  show ?thesis by (intro conjI division_closure_stage_member[OF add_stage] division_closure_stage_member[OF mult_stage])
qed
lemma division_closure_add:
  "x \<in> division_closure S \<Longrightarrow> y \<in> division_closure S \<Longrightarrow> x+y \<in> division_closure S"
  using division_closure_binary by blast
lemma division_closure_mult:
  "x \<in> division_closure S \<Longrightarrow> y \<in> division_closure S \<Longrightarrow> x*y \<in> division_closure S"
  using division_closure_binary by blast
lemma division_closure_is_division_subring:
  "division_subring_on (division_closure S)"
  unfolding division_subring_on_def
  by (auto intro: division_closure_zero division_closure_one division_closure_neg
      division_closure_inverse division_closure_add division_closure_mult)

lemma division_closure_least:
  assumes E: "division_subring_on E" and S: "S \<subseteq> E"
  shows "division_closure S \<subseteq> E"
proof -
  have stage: "division_closure_stage S n \<subseteq> E" for n
  proof (induction n)
    case 0 show ?case using E S by (auto simp: division_subring_on_def)
  next
    case (Suc n)
    have binary: "a+b \<in> E \<and> a*b \<in> E"
      if "a \<in> division_closure_stage S n" "b \<in> division_closure_stage S n" for a b
    proof -
      have aE: "a \<in> E" by (rule subsetD[OF Suc.IH that(1)])
      have bE: "b \<in> E" by (rule subsetD[OF Suc.IH that(2)])
      show ?thesis using E aE bE unfolding division_subring_on_def by blast
    qed
    have add_closed: "a+b \<in> E"
      if "a \<in> division_closure_stage S n" "b \<in> division_closure_stage S n" for a b
      using binary[OF that] by blast
    have mult_closed: "a*b \<in> E"
      if "a \<in> division_closure_stage S n" "b \<in> division_closure_stage S n" for a b
      using binary[OF that] by blast
    show ?case using Suc.IH E by (auto simp: division_subring_on_def intro: add_closed mult_closed)
  qed
  show ?thesis using stage unfolding division_closure_def by blast
qed

lemma division_closure_intersection:
  "division_closure S = \<Inter>{E. division_subring_on E \<and> S \<subseteq> E}"
proof (rule subset_antisym)
  show "division_closure S \<subseteq> \<Inter>{E. division_subring_on E \<and> S \<subseteq> E}"
  proof (rule Inter_greatest)
    fix X assume X: "X \<in> {E. division_subring_on E \<and> S \<subseteq> E}"
    have closed: "division_subring_on X" and contains: "S \<subseteq> X" using X by auto
    show "division_closure S \<subseteq> X" by (rule division_closure_least[OF closed contains])
  qed
  show "\<Inter>{E. division_subring_on E \<and> S \<subseteq> E} \<subseteq> division_closure S"
    by (rule Inter_lower) (simp add: division_closure_is_division_subring division_closure_contains)
qed

lemma finite_division_closure_stage:
  "finite S \<Longrightarrow> finite (division_closure_stage S n)"
  by (induction n) simp_all
lemma countable_division_closure_stage:
  "countable S \<Longrightarrow> countable (division_closure_stage S n)"
  by (induction n) simp_all

theorem countable_division_closure:
  assumes "countable S"
  shows "countable (division_closure S)"
  unfolding division_closure_def
  by (intro countable_UN countableI_type countable_division_closure_stage assms)

end
