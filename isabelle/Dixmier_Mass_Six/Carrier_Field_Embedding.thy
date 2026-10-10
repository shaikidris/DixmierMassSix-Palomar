theory Carrier_Field_Embedding
  imports "Division_Subring_Closure"
begin

locale dixmier_carrier_field_embedding =
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> 'l::field"
  assumes carrier_closed: "division_subring_on E"
    and map_one: "f 1 = 1"
    and map_add_on: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> f (a+b) = f a + f b"
    and map_mult_on: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> f (a*b) = f a * f b"
    and injective_on: "inj_on f E"
begin

lemma E_zero [simp]: "0 \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_one [simp]: "1 \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_neg: "a \<in> E \<Longrightarrow> -a \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_inverse: "a \<in> E \<Longrightarrow> inverse a \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_add: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> a+b \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_mult: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> a*b \<in> E"
  using carrier_closed unfolding division_subring_on_def by blast
lemma E_diff: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> a-b \<in> E"
  unfolding diff_conv_add_uminus by (intro E_add E_neg)
lemma E_divide: "a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> a/b \<in> E"
  unfolding divide_inverse by (intro E_mult E_inverse)
lemma E_sum:
  assumes "finite J" "\<And>j. j \<in> J \<Longrightarrow> a j \<in> E"
  shows "(\<Sum>j\<in>J. a j) \<in> E"
  using assms by (induction J rule: finite_induct) (auto intro: E_add)

lemma map_zero [simp]: "f 0 = 0"
proof -
  have "f 0 + 0 = f 0 + f 0" using map_add_on[OF E_zero E_zero] by simp
  then show ?thesis by (simp only: add_left_cancel)
qed
lemma map_eq_zero_on:
  assumes a: "a \<in> E"
  shows "f a = 0 \<longleftrightarrow> a = 0"
proof
  assume "f a = 0"
  then have eq: "f a = f 0" by (simp only: map_zero)
  show "a=0" by (rule inj_onD[OF injective_on eq a E_zero])
next
  assume "a=0"
  then show "f a=0" by (simp only: map_zero)
qed
lemma map_neg_on:
  assumes "a \<in> E"
  shows "f (-a) = - f a"
proof -
  have "f a + f (-a) = 0"
    using map_add_on[OF assms E_neg[OF assms]] by simp
  then show ?thesis by (simp only: add_eq_0_iff)
qed
lemma map_diff_on:
  assumes a: "a \<in> E" and b: "b \<in> E"
  shows "f (a-b) = f a-f b"
  unfolding diff_conv_add_uminus
  by (simp only: map_add_on[OF a E_neg[OF b]] map_neg_on[OF b])
lemma map_inverse_on:
  assumes a: "a \<in> E"
  shows "f (inverse a) = inverse (f a)"
proof (cases "a=0")
  case True then show ?thesis by simp
next
  case False
  have nz: "f a \<noteq> 0" using map_eq_zero_on[OF a] False by simp
  have "f a * f (inverse a) = 1"
    using map_mult_on[OF a E_inverse[OF a]] False map_one by simp
  then show ?thesis by (rule inverse_unique[symmetric])
qed
lemma map_sum_on:
  assumes "finite J" "\<And>j. j \<in> J \<Longrightarrow> a j \<in> E"
  shows "f (\<Sum>j\<in>J. a j) = (\<Sum>j\<in>J. f (a j))"
  using assms by (induction J rule: finite_induct) (auto simp: map_add_on E_sum)

end
end
