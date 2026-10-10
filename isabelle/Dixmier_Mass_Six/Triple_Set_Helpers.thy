theory Triple_Set_Helpers
  imports "Support_Subset_Products"
begin

lemma sum_triple:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows "(\<Sum>m\<in>{a,b,c}. f m) = f a + f b + f c"
  using assms by (simp add: add.assoc)

lemma erase_triple_fst:
  assumes "a \<noteq> b" "a \<noteq> c"
  shows "({a,b,c}::nat set) - {a} = {b,c}"
  using assms by auto

lemma erase_triple_snd:
  assumes "a \<noteq> b" "b \<noteq> c"
  shows "({a,b,c}::nat set) - {b} = {a,c}"
  using assms by auto

lemma erase_triple_thd:
  assumes "a \<noteq> c" "b \<noteq> c"
  shows "({a,b,c}::nat set) - {c} = {a,b}"
  using assms by auto

end
