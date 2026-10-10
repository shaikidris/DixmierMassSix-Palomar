theory Shared_Coefficient_Carrier
  imports "Division_Subring_Closure"
begin

definition rational_generated_carrier :: "'a::field_char_0 set \<Rightarrow> 'a set" where
  "rational_generated_carrier A = division_closure (A \<union> range of_rat)"

lemma rational_generated_carrier_closed:
  "division_subring_on (rational_generated_carrier A)"
  unfolding rational_generated_carrier_def by (rule division_closure_is_division_subring)

lemma rational_generated_carrier_generator:
  "x \<in> A \<Longrightarrow> x \<in> rational_generated_carrier A"
  unfolding rational_generated_carrier_def
  by (rule division_closure_generator) auto

lemma rational_generated_carrier_rationals:
  "range of_rat \<subseteq> rational_generated_carrier A"
  unfolding rational_generated_carrier_def
  by (auto intro: division_closure_generator)

theorem countable_rational_generated_carrier:
  fixes A :: "'a::field_char_0 set"
  assumes "finite A"
  shows "countable (rational_generated_carrier A)"
proof -
  have finite_countable: "countable A" by (rule countable_finite[OF assms])
  have rational_countable: "countable (range (of_rat :: rat \<Rightarrow> 'a::field_char_0))"
    by (intro countable_image countableI_type)
  show ?thesis
    unfolding rational_generated_carrier_def
    by (intro countable_division_closure countable_Un finite_countable rational_countable)
qed

theorem exists_countable_rational_carrier_for_pair:
  assumes P: "P \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q \<in> weyl_algebra"
  shows "\<exists>E c d. division_subring_on E \<and> countable E \<and> range of_rat \<subseteq> E \<and>
    finite {u. c u \<noteq> 0} \<and> finite {u. d u \<noteq> 0} \<and>
    finite_normal_sum {u. c u \<noteq> 0} c = P \<and> finite_normal_sum {u. d u \<noteq> 0} d = Q \<and>
    (\<forall>u\<in>{u. c u \<noteq> 0}. c u \<in> E) \<and> (\<forall>u\<in>{u. d u \<noteq> 0}. d u \<in> E)"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and cP: "finite_normal_sum {u. c u \<noteq> 0} c = P"
    using weyl_exists_finite_coordinates[OF P] by blast
  obtain d where df: "finite {u. d u \<noteq> 0}" and dQ: "finite_normal_sum {u. d u \<noteq> 0} d = Q"
    using weyl_exists_finite_coordinates[OF Q] by blast
  let ?A = "c ` {u. c u \<noteq> 0} \<union> d ` {u. d u \<noteq> 0}"
  let ?E = "rational_generated_carrier ?A"
  have finite_A: "finite ?A" using cf df by simp
  have closed: "division_subring_on ?E" by (rule rational_generated_carrier_closed)
  have count: "countable ?E" by (rule countable_rational_generated_carrier[OF finite_A])
  have rationals: "range of_rat \<subseteq> ?E" by (rule rational_generated_carrier_rationals)
  have c_member: "\<forall>u\<in>{u. c u \<noteq> 0}. c u \<in> ?E"
    by (intro ballI rational_generated_carrier_generator) auto
  have d_member: "\<forall>u\<in>{u. d u \<noteq> 0}. d u \<in> ?E"
    by (intro ballI rational_generated_carrier_generator) auto
  show ?thesis
  proof (rule exI[of _ ?E], rule exI[of _ c], rule exI[of _ d], intro conjI)
    show "division_subring_on ?E" by (rule closed)
  next
    show "countable ?E" by (rule count)
  next
    show "range of_rat \<subseteq> ?E" by (rule rationals)
  next
    show "finite {u. c u \<noteq> 0}" by (rule cf)
  next
    show "finite {u. d u \<noteq> 0}" by (rule df)
  next
    show "finite_normal_sum {u. c u \<noteq> 0} c = P" by (rule cP)
  next
    show "finite_normal_sum {u. d u \<noteq> 0} d = Q" by (rule dQ)
  next
    show "\<forall>u\<in>{u. c u \<noteq> 0}. c u \<in> ?E" by (rule c_member)
  next
    show "\<forall>u\<in>{u. d u \<noteq> 0}. d u \<in> ?E" by (rule d_member)
  qed
qed

theorem exists_countable_pbw_coefficient_carrier:
  assumes P: "P \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q \<in> weyl_algebra"
  shows "\<exists>E. division_subring_on E \<and> countable E \<and> range of_rat \<subseteq> E \<and>
    (\<forall>a b. pbw_coeff P a b \<in> E \<and> pbw_coeff Q a b \<in> E)"
proof -
  obtain E c d where closed: "division_subring_on E" and count: "countable E"
    and rats: "range of_rat \<subseteq> E"
    and cf: "finite {u. c u \<noteq> 0}" and df: "finite {u. d u \<noteq> 0}"
    and cP: "finite_normal_sum {u. c u \<noteq> 0} c = P"
    and dQ: "finite_normal_sum {u. d u \<noteq> 0} d = Q"
    and cm: "\<forall>u\<in>{u. c u \<noteq> 0}. c u \<in> E"
    and dm: "\<forall>u\<in>{u. d u \<noteq> 0}. d u \<in> E"
    using exists_countable_rational_carrier_for_pair[OF P Q] by blast
  have zero: "0 \<in> E" using closed unfolding division_subring_on_def by blast
  have cin: "c u \<in> E" for u
  proof (cases "c u = 0")
    case True then show ?thesis using zero by simp
  next
    case False
    have "u \<in> {u. c u \<noteq> 0}" using False by simp
    then show ?thesis by (rule bspec[OF cm])
  qed
  have din: "d u \<in> E" for u
  proof (cases "d u = 0")
    case True then show ?thesis using zero by simp
  next
    case False
    have "u \<in> {u. d u \<noteq> 0}" using False by simp
    then show ?thesis by (rule bspec[OF dm])
  qed
  have coeffP: "pbw_coeff P a b = c (a,b)" for a b
    using pbw_coeff_finite_coordinates[OF cf, of a b] cP by simp
  have coeffQ: "pbw_coeff Q a b = d (a,b)" for a b
    using pbw_coeff_finite_coordinates[OF df, of a b] dQ by simp
  have all_coefficients: "\<forall>a b. pbw_coeff P a b \<in> E \<and> pbw_coeff Q a b \<in> E"
    by (simp add: coeffP coeffQ cin din)
  show ?thesis
    by (rule exI[of _ E]) (simp only: closed count rats all_coefficients simp_thms)
qed

end
