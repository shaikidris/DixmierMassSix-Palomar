theory PBW_Finite_Coordinates
  imports PBW_Recovery
begin

definition normal_list_coeff :: "((nat \<times> nat) \<times> 'a::field) list \<Rightarrow> nat \<times> nat \<Rightarrow> 'a" where
  "normal_list_coeff ts u = sum_list (map (\<lambda>t. if fst t = u then snd t else 0) ts)"
definition finite_normal_sum :: "(nat \<times> nat) set \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a::field) \<Rightarrow> 'a poly_operator" where
  "finite_normal_sum S c = (\<lambda>p. \<Sum>u\<in>S. smult (c u) (normal_monomial (fst u) (snd u) p))"
lemma finite_normal_sum_zero [simp]: "finite_normal_sum S (\<lambda>_. 0) = 0"
  by (rule ext) (simp add: finite_normal_sum_def)
lemma finite_normal_sum_add:
  "finite_normal_sum S (\<lambda>u. c u + d u) = finite_normal_sum S c + finite_normal_sum S d"
  by (rule ext) (simp add: finite_normal_sum_def smult_add_left sum.distrib)
lemma finite_normal_sum_single:
  assumes "finite S" "u \<in> S"
  shows "finite_normal_sum S (\<lambda>v. if v = u then c else 0) =
    (\<lambda>p. smult c (normal_monomial (fst u) (snd u) p))"
proof -
  have hterm: "smult (if v = u then c else 0) (normal_monomial (fst v) (snd v) p) =
    (if v = u then smult c (normal_monomial (fst u) (snd u) p) else 0)" for v p
    by auto
  show ?thesis using assms by (rule_tac ext) (simp add: finite_normal_sum_def hterm sum.delta)
qed
lemma normal_list_coeff_Nil [simp]: "normal_list_coeff [] u = 0"
  by (simp add: normal_list_coeff_def)
lemma normal_list_coeff_Cons:
  "normal_list_coeff (t#ts) u = (if fst t = u then snd t else 0) + normal_list_coeff ts u"
  by (simp add: normal_list_coeff_def)
lemma normal_list_Cons:
  "normal_list (t#ts) = (\<lambda>p. smult (snd t) (normal_monomial (fst (fst t)) (snd (fst t)) p)) + normal_list ts"
  by (rule ext) (simp add: normal_list_def)
lemma normal_list_as_finite_sum:
  assumes "finite S" "fst ` set ts \<subseteq> S"
  shows "normal_list ts = finite_normal_sum S (normal_list_coeff ts)"
  using assms(2)
proof (induction ts)
  case Nil then show ?case by (simp add: normal_list_coeff_def)
next
  case (Cons t ts)
  have key: "fst t \<in> S" and tail: "fst ` set ts \<subseteq> S" using Cons.prems by auto
  have coords: "normal_list_coeff (t#ts) =
    (\<lambda>u. (if u = fst t then snd t else 0) + normal_list_coeff ts u)"
    by (rule ext) (simp add: normal_list_coeff_Cons eq_commute)
  show ?case
    unfolding coords finite_normal_sum_add finite_normal_sum_single[OF assms(1) key]
      normal_list_Cons Cons.IH[OF tail] by simp
qed
lemma pbw_coeff_normal_list:
  "pbw_coeff (normal_list ts :: 'a::field_char_0 poly_operator) i j = normal_list_coeff ts (i,j)"
proof (induction ts)
  case Nil show ?case by (simp add: pbw_coeff_def zero_fun_def[symmetric])
next
  case (Cons t ts)
  show ?case
    by (simp only: normal_list_Cons pbw_coeff_add pbw_coeff_smult
      pbw_coeff_normal_monomial normal_list_coeff_Cons Cons.IH; auto simp: prod_eq_iff)
qed

lemma finite_normal_sum_empty [simp]: "finite_normal_sum {} c = 0"
  by (rule ext) (simp add: finite_normal_sum_def)
lemma finite_normal_sum_insert:
  "finite S \<Longrightarrow> u \<notin> S \<Longrightarrow> finite_normal_sum (insert u S) c =
    (\<lambda>p. smult (c u) (normal_monomial (fst u) (snd u) p)) + finite_normal_sum S c"
  by (rule ext) (simp add: finite_normal_sum_def)
lemma pbw_coeff_finite_normal_sum:
  assumes "finite S"
  shows "pbw_coeff (finite_normal_sum S c :: 'a::field_char_0 poly_operator) i j =
    (if (i,j) \<in> S then c (i,j) else 0)"
  using assms
proof (induction S)
  case empty show ?case by (simp add: pbw_coeff_def zero_fun_def[symmetric])
next
  case (insert u S)
  show ?case
    unfolding finite_normal_sum_insert[OF insert.hyps]
    by (simp only: pbw_coeff_add pbw_coeff_smult pbw_coeff_normal_monomial insert.IH;
      use insert.hyps in \<open>auto simp: prod_eq_iff split: if_splits\<close>)
qed
lemma normal_list_coeff_outside:
  "u \<notin> fst ` set ts \<Longrightarrow> normal_list_coeff ts u = 0"
  by (induction ts) (auto simp: normal_list_coeff_def)
lemma weyl_pbw_finite_support:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "finite {u. pbw_coeff T (fst u) (snd u) \<noteq> 0}"
proof -
  obtain ts where T: "T = normal_list ts" using weyl_finite_normal_expansion[OF assms] by blast
  have "{u. pbw_coeff T (fst u) (snd u) \<noteq> 0} \<subseteq> fst ` set ts"
    unfolding T pbw_coeff_normal_list by (auto dest: normal_list_coeff_outside)
  then show ?thesis by (rule finite_subset) simp
qed
lemma weyl_pbw_reconstruction:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "\<exists>S. finite S \<and> T = finite_normal_sum S (\<lambda>u. pbw_coeff T (fst u) (snd u))"
proof -
  obtain ts where T: "T = normal_list ts" using weyl_finite_normal_expansion[OF assms] by blast
  show ?thesis
    by (rule exI[of _ "fst ` set ts"])
       (simp add: T pbw_coeff_normal_list normal_list_as_finite_sum)
qed
lemma finite_normal_sum_injective_on:
  assumes "finite S"
    and "finite_normal_sum S c = (finite_normal_sum S d :: 'a::field_char_0 poly_operator)"
    and "u \<in> S"
  shows "c u = d u"
proof -
  have "pbw_coeff (finite_normal_sum S c) (fst u) (snd u) =
    pbw_coeff (finite_normal_sum S d) (fst u) (snd u)" using assms(2) by simp
  then show ?thesis using assms(1,3) by (simp add: pbw_coeff_finite_normal_sum)
qed

lemma finite_normal_sum_restrict_support:
  assumes "finite S" "{u. c u \<noteq> 0} \<subseteq> S"
  shows "finite_normal_sum S c = finite_normal_sum {u. c u \<noteq> 0} c"
  unfolding finite_normal_sum_def
  by (rule ext, rule sum.mono_neutral_right[OF assms]) auto
lemma weyl_exists_finite_coordinates:
  assumes "T \<in> (weyl_algebra :: 'a::field poly_operator set)"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> finite_normal_sum {u. c u \<noteq> 0} c = T"
proof -
  obtain ts where T: "T = normal_list ts" using weyl_finite_normal_expansion[OF assms] by blast
  let ?c = "normal_list_coeff ts"
  let ?S = "fst ` set ts"
  have sub: "{u. ?c u \<noteq> 0} \<subseteq> ?S" by (auto dest: normal_list_coeff_outside)
  have fin: "finite {u. ?c u \<noteq> 0}" by (rule finite_subset[OF sub]) simp
  have rep: "T = finite_normal_sum ?S ?c"
    unfolding T by (rule normal_list_as_finite_sum) auto
  show ?thesis
    by (rule exI[of _ ?c])
       (use fin rep finite_normal_sum_restrict_support[OF _ sub] in auto)
qed
lemma pbw_coeff_finite_coordinates:
  assumes "finite {u. c u \<noteq> 0}"
  shows "pbw_coeff (finite_normal_sum {u. c u \<noteq> 0} c :: 'a::field_char_0 poly_operator) i j = c (i,j)"
  by (simp add: pbw_coeff_finite_normal_sum[OF assms])
lemma finite_coordinates_unique:
  assumes "finite {u. c u \<noteq> 0}" "finite {u. d u \<noteq> 0}"
    "finite_normal_sum {u. c u \<noteq> 0} c = (finite_normal_sum {u. d u \<noteq> 0} d :: 'a::field_char_0 poly_operator)"
  shows "c = d"
proof (rule ext)
  fix u
  have "pbw_coeff (finite_normal_sum {u. c u \<noteq> 0} c) (fst u) (snd u) =
    pbw_coeff (finite_normal_sum {u. d u \<noteq> 0} d) (fst u) (snd u)"
    using assms(3) by simp
  then show "c u = d u" by (simp add: pbw_coeff_finite_coordinates[OF assms(1)] pbw_coeff_finite_coordinates[OF assms(2)])
qed

lemma weyl_pbw_injective:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
    "\<And>i j. pbw_coeff T i j = pbw_coeff U i j"
  shows "T = U"
proof -
  obtain c where cfin: "finite {u. c u \<noteq> 0}" and cT: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF assms(1)] by blast
  obtain d where dfin: "finite {u. d u \<noteq> 0}" and dU: "finite_normal_sum {u. d u \<noteq> 0} d = U"
    using weyl_exists_finite_coordinates[OF assms(2)] by blast
  have cd: "c = d"
  proof (rule ext)
    fix u
    have "c u = pbw_coeff T (fst u) (snd u)"
      using pbw_coeff_finite_coordinates[OF cfin, of "fst u" "snd u"] cT by simp
    also have "... = pbw_coeff U (fst u) (snd u)" by (rule assms(3))
    also have "... = d u" using pbw_coeff_finite_coordinates[OF dfin, of "fst u" "snd u"] dU by simp
    finally show "c u = d u" .
  qed
  show ?thesis using cT dU cd by simp
qed

lemma finite_normal_sum_in_weyl:
  "finite S \<Longrightarrow> finite_normal_sum S c \<in> weyl_algebra"
proof (induction S rule: finite_induct)
  case empty show ?case by (simp add: weyl_algebra_def zero_fun_def[symmetric])
next
  case (insert u S)
  have left: "(\<lambda>p. smult (c u) (normal_monomial (fst u) (snd u) p)) \<in> weyl_algebra"
    using normal_monomial_in_weyl[of "fst u" "snd u"]
    unfolding weyl_algebra_def by (rule op_adjoin_smult)
  have "(\<lambda>p. smult (c u) (normal_monomial (fst u) (snd u) p)) + finite_normal_sum S c \<in> weyl_algebra"
    using left insert.IH unfolding weyl_algebra_def by (rule op_adjoin.add)
  then show ?case by (simp only: finite_normal_sum_insert[OF insert.hyps])
qed

end
