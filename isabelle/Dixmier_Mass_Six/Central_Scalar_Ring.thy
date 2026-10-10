theory Central_Scalar_Ring
  imports "Abstract_Weyl_Quotient"
begin

text \<open>The target ring can be noncommutative, have a proper carrier and
be trivial. The scalar map is not assumed injective.\<close>

definition central_lcomb :: "('a,'r) ring_scheme \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow>
    ('i \<Rightarrow> 'a) \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'k) \<Rightarrow> 'a" where
  "central_lcomb R s B S c = finsum R (\<lambda>u. monoid.mult R (s (c u)) (B u)) S"

locale central_scalar_ring =
  scalar: ring_hom_ring "(nc_type_ring :: 'k::field ring)" R s
  for R :: "('a,'r) ring_scheme" and s :: "'k::field \<Rightarrow> 'a" +
  assumes scalar_central: "\<And>c z. z \<in> carrier R \<Longrightarrow>
    monoid.mult R (s c) z = monoid.mult R z (s c)"
begin

lemma scalar_closed: "s c \<in> carrier R"
  by (rule scalar.hom_closed) (simp only: nc_type_ring_def ring_record_simps UNIV_I)
lemma scalar_zero: "s 0 = ring.zero R"
  using scalar.hom_zero by (simp only: nc_type_ring_def ring_record_simps)
lemma scalar_one: "s 1 = monoid.one R"
  using scalar.hom_one by (simp only: nc_type_ring_def ring_record_simps)
lemma scalar_add: "s (a+b) = ring.add R (s a) (s b)"
  using scalar.hom_add[of a b] by (simp only: nc_type_ring_def ring_record_simps UNIV_I)
lemma scalar_mult: "s (a*b) = monoid.mult R (s a) (s b)"
  using scalar.hom_mult[of a b] by (simp only: nc_type_ring_def ring_record_simps UNIV_I)

lemma lcomb_term_closed:
  "b \<in> carrier R \<Longrightarrow> monoid.mult R (s c) b \<in> carrier R"
  by (rule scalar.S.m_closed[OF scalar_closed])
lemma lcomb_terms_closed:
  "B \<in> S \<rightarrow> carrier R \<Longrightarrow>
    (\<lambda>u. monoid.mult R (s (c u)) (B u)) \<in> S \<rightarrow> carrier R"
  by (auto simp only: Pi_def intro: lcomb_term_closed)
lemma lcomb_closed:
  "B \<in> S \<rightarrow> carrier R \<Longrightarrow> central_lcomb R s B S c \<in> carrier R"
  unfolding central_lcomb_def by (rule scalar.S.finsum_closed) (rule lcomb_terms_closed)
lemma lcomb_empty: "central_lcomb R s B {} c = ring.zero R"
  by (simp only: central_lcomb_def scalar.S.finsum_empty)
lemma lcomb_insert:
  assumes "finite S" "u \<notin> S" "B \<in> insert u S \<rightarrow> carrier R"
  shows "central_lcomb R s B (insert u S) c =
    ring.add R (monoid.mult R (s (c u)) (B u)) (central_lcomb R s B S c)"
  unfolding central_lcomb_def
  by (rule scalar.S.finsum_insert[OF assms(1,2)])
     (use assms(3) in \<open>auto simp only: Pi_def intro: lcomb_term_closed\<close>)

lemma lcomb_cong:
  assumes "B \<in> S \<rightarrow> carrier R" "\<And>u. u \<in> S \<Longrightarrow> c u = d u"
  shows "central_lcomb R s B S c = central_lcomb R s B S d"
  unfolding central_lcomb_def
  by (rule scalar.S.finsum_cong'[OF refl lcomb_terms_closed[OF assms(1)]])
     (simp only: assms(2))

lemma lcomb_zero:
  assumes "B \<in> S \<rightarrow> carrier R"
  shows "central_lcomb R s B S (\<lambda>_. 0) = ring.zero R"
proof -
  have "central_lcomb R s B S (\<lambda>_. 0) = finsum R (\<lambda>_. ring.zero R) S"
    unfolding central_lcomb_def
  proof (rule scalar.S.finsum_cong'[OF refl])
    show "(\<lambda>_. ring.zero R) \<in> S \<rightarrow> carrier R" by (auto simp: Pi_def)
    show "\<And>u. u \<in> S \<Longrightarrow> monoid.mult R (s 0) (B u) = ring.zero R"
      using assms by (auto simp only: Pi_def scalar_zero intro: scalar.S.l_null)
  qed
  then show ?thesis by (simp only: scalar.S.finsum_zero)
qed

lemma lcomb_add:
  assumes B: "B \<in> S \<rightarrow> carrier R"
  shows "central_lcomb R s B S (\<lambda>u. c u + d u) =
    ring.add R (central_lcomb R s B S c) (central_lcomb R s B S d)"
proof -
  have term_eq: "monoid.mult R (s (c u + d u)) (B u) =
    ring.add R (monoid.mult R (s (c u)) (B u)) (monoid.mult R (s (d u)) (B u))"
    if "u \<in> S" for u
  proof -
    have Bu: "B u \<in> carrier R" using B that by (simp add: Pi_def)
    show ?thesis unfolding scalar_add
      by (rule scalar.S.l_distr[OF scalar_closed scalar_closed Bu])
  qed
  have closed: "(\<lambda>u. ring.add R (monoid.mult R (s (c u)) (B u))
      (monoid.mult R (s (d u)) (B u))) \<in> S \<rightarrow> carrier R"
    using B by (auto simp only: Pi_def intro: scalar.S.a_closed lcomb_term_closed)
  have "central_lcomb R s B S (\<lambda>u. c u+d u) =
    finsum R (\<lambda>u. ring.add R (monoid.mult R (s (c u)) (B u))
      (monoid.mult R (s (d u)) (B u))) S"
    unfolding central_lcomb_def by (rule scalar.S.finsum_cong'[OF refl closed]) (rule term_eq)
  also have "... = ring.add R (central_lcomb R s B S c) (central_lcomb R s B S d)"
    unfolding central_lcomb_def by (rule scalar.S.finsum_addf[OF lcomb_terms_closed[OF B] lcomb_terms_closed[OF B]])
  finally show ?thesis .
qed

lemma lcomb_scale:
  assumes fin: "finite S" and B: "B \<in> S \<rightarrow> carrier R"
  shows "central_lcomb R s B S (\<lambda>u. d * c u) =
    monoid.mult R (s d) (central_lcomb R s B S c)"
proof -
  have closed: "(\<lambda>u. monoid.mult R (s d) (monoid.mult R (s (c u)) (B u))) \<in> S \<rightarrow> carrier R"
    using B by (auto simp only: Pi_def intro: scalar.S.m_closed scalar_closed lcomb_term_closed)
  have "central_lcomb R s B S (\<lambda>u. d*c u) =
    finsum R (\<lambda>u. monoid.mult R (s d) (monoid.mult R (s (c u)) (B u))) S"
    unfolding central_lcomb_def
  proof (rule scalar.S.finsum_cong'[OF refl closed])
    fix u assume "u \<in> S"
    then have "B u \<in> carrier R" using B by (simp add: Pi_def)
    then show "monoid.mult R (s (d*c u)) (B u) =
      monoid.mult R (s d) (monoid.mult R (s (c u)) (B u))"
      by (simp only: scalar_mult; rule scalar.S.m_assoc[OF scalar_closed scalar_closed])
  qed
  also have "... = monoid.mult R (s d) (central_lcomb R s B S c)"
    unfolding central_lcomb_def
    by (rule scalar.S.finsum_rdistr[OF fin scalar_closed lcomb_terms_closed[OF B], symmetric])
  finally show ?thesis .
qed

lemma lcomb_single:
  assumes uS: "u \<in> S" and fin: "finite S" and B: "B \<in> S \<rightarrow> carrier R"
  shows "central_lcomb R s B S (\<lambda>v. if v=u then c else 0) = monoid.mult R (s c) (B u)"
proof -
  have terms: "(\<lambda>v. monoid.mult R (s c) (B v)) \<in> S \<rightarrow> carrier R"
    by (rule lcomb_terms_closed[OF B])
  have cond: "(\<lambda>v. if u=v then monoid.mult R (s c) (B v) else ring.zero R) \<in> S \<rightarrow> carrier R"
    using terms by (auto simp only: Pi_def intro: scalar.S.zero_closed split: if_splits)
  have "central_lcomb R s B S (\<lambda>v. if v=u then c else 0) =
    finsum R (\<lambda>v. if u=v then monoid.mult R (s c) (B v) else ring.zero R) S"
    unfolding central_lcomb_def
  proof (rule scalar.S.finsum_cong'[OF refl cond])
    fix v assume vS: "v \<in> S"
    have Bv: "B v \<in> carrier R" using B vS by (simp add: Pi_def)
    show "monoid.mult R (s (if v=u then c else 0)) (B v) =
      (if u=v then monoid.mult R (s c) (B v) else ring.zero R)"
      by (cases "u=v") (simp_all only: if_True if_False eq_commute scalar_zero scalar.S.l_null[OF Bv] simp_thms)
  qed
  also have "... = monoid.mult R (s c) (B u)"
    by (rule scalar.S.finsum_singleton[OF uS fin terms])
  finally show ?thesis .
qed

lemma lcomb_extend:
  assumes fin: "finite T" and ST: "S \<subseteq> T" and B: "B \<in> T \<rightarrow> carrier R"
    and outside: "\<And>u. u \<in> T-S \<Longrightarrow> c u = 0"
  shows "central_lcomb R s B S c = central_lcomb R s B T c"
  unfolding central_lcomb_def finsum_def
proof (rule comm_monoid.finprod_mono_neutral_cong_left[OF scalar.S.a_comm_monoid fin ST])
  show "\<And>u. u \<in> T-S \<Longrightarrow> monoid.mult R (s (c u)) (B u) = monoid.one (add_monoid R)"
    using outside B by (auto simp only: Pi_def scalar_zero monoid_record_simps intro: scalar.S.l_null)
  show "\<And>u. u \<in> S \<Longrightarrow> monoid.mult R (s (c u)) (B u) = monoid.mult R (s (c u)) (B u)" by (rule refl)
  show "(\<lambda>u. monoid.mult R (s (c u)) (B u)) \<in> T \<rightarrow> carrier (add_monoid R)"
    using lcomb_terms_closed[OF B, of c] by (simp only: monoid_record_simps)
qed

lemma lcomb_restrict_support:
  assumes "finite S" "B \<in> S \<rightarrow> carrier R" "{u. c u \<noteq> 0} \<subseteq> S"
  shows "central_lcomb R s B S c = central_lcomb R s B {u. c u \<noteq> 0} c"
  by (rule lcomb_extend[OF assms(1,3,2), symmetric]) auto

end
end
