theory Ideal_Quotient_Lift
  imports "HOL-Algebra.QuotRing"
begin

text \<open>The ideal below need only be contained in the kernel. It is never
replaced by the full kernel. Definite description is used only after proving
that the image of every valid coset is a singleton.\<close>

definition ideal_quotient_lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "ideal_quotient_lift h C = the_elem (h ` C)"

locale contained_ideal_quotient =
  H: ring_hom_ring R S h + J: ideal I R
  for R and S and h and I +
  assumes ideal_in_kernel: "I \<subseteq> a_kernel R S h"
begin

lemma ideal_image_zero:
  assumes "i \<in> I"
  shows "h i = ring.zero S"
proof -
  have "i \<in> a_kernel R S h" by (rule subsetD[OF ideal_in_kernel assms])
  then have "i \<in> carrier R \<and> h i = ring.zero S"
    by (simp only: a_kernel_def' mem_Collect_eq)
  then show ?thesis by (rule conjunct2)
qed

lemma coset_image_singleton:
  assumes a: "a \<in> carrier R"
  shows "h ` a_r_coset R I a = {h a}"
proof -
  have equal: "h (ring.add R i a) = h a" if "i \<in> I" for i
    using a J.Icarr[OF that] ideal_image_zero[OF that]
    by (simp add: H.hom_add)
  have self: "a \<in> a_r_coset R I a" by (rule J.a_rcos_self[OF a])
  show ?thesis using equal self
    by (auto simp: a_r_coset_def')
qed

lemma quotient_carrier_rep:
  "C \<in> carrier (FactRing R I) \<Longrightarrow>
    \<exists>a\<in>carrier R. C = a_r_coset R I a"
  by (auto simp: FactRing_def A_RCOSETS_def')

lemma quotient_mk_closed:
  "a \<in> carrier R \<Longrightarrow> a_r_coset R I a \<in> carrier (FactRing R I)"
  by (auto simp: FactRing_def A_RCOSETS_def')

lemma quotient_lift_mk:
  "a \<in> carrier R \<Longrightarrow> ideal_quotient_lift h (a_r_coset R I a) = h a"
  by (simp add: ideal_quotient_lift_def coset_image_singleton)

lemma quotient_lift_closed:
  assumes "C \<in> carrier (FactRing R I)"
  shows "ideal_quotient_lift h C \<in> carrier S"
proof -
  obtain a where a: "a \<in> carrier R" and C: "C = a_r_coset R I a"
    using quotient_carrier_rep[OF assms] by blast
  have "h a \<in> carrier S" by (rule H.hom_closed[OF a])
  then show ?thesis by (simp only: C quotient_lift_mk[OF a])
qed

lemma quotient_lift_ring_hom:
  "ideal_quotient_lift h \<in> ring_hom (FactRing R I) S"
proof (rule ring_hom_memI)
  show "\<And>C. C \<in> carrier (FactRing R I) \<Longrightarrow> ideal_quotient_lift h C \<in> carrier S"
    by (rule quotient_lift_closed)
  show "\<And>C D. C \<in> carrier (FactRing R I) \<Longrightarrow> D \<in> carrier (FactRing R I) \<Longrightarrow>
    ideal_quotient_lift h (monoid.mult (FactRing R I) C D) =
    monoid.mult S (ideal_quotient_lift h C) (ideal_quotient_lift h D)"
  proof -
    fix C D assume c: "C \<in> carrier (FactRing R I)" and d: "D \<in> carrier (FactRing R I)"
    obtain a where a: "a \<in> carrier R" and C: "C = a_r_coset R I a"
      using quotient_carrier_rep[OF c] by blast
    obtain b where b: "b \<in> carrier R" and D: "D = a_r_coset R I b"
      using quotient_carrier_rep[OF d] by blast
    show "ideal_quotient_lift h (monoid.mult (FactRing R I) C D) =
      monoid.mult S (ideal_quotient_lift h C) (ideal_quotient_lift h D)"
      by (simp add: C D FactRing_def J.rcoset_mult_add[OF a b]
        quotient_lift_mk a b H.hom_mult)
  qed
  show "\<And>C D. C \<in> carrier (FactRing R I) \<Longrightarrow> D \<in> carrier (FactRing R I) \<Longrightarrow>
    ideal_quotient_lift h (ring.add (FactRing R I) C D) =
    ring.add S (ideal_quotient_lift h C) (ideal_quotient_lift h D)"
  proof -
    fix C D assume c: "C \<in> carrier (FactRing R I)" and d: "D \<in> carrier (FactRing R I)"
    obtain a where a: "a \<in> carrier R" and C: "C = a_r_coset R I a"
      using quotient_carrier_rep[OF c] by blast
    obtain b where b: "b \<in> carrier R" and D: "D = a_r_coset R I b"
      using quotient_carrier_rep[OF d] by blast
    show "ideal_quotient_lift h (ring.add (FactRing R I) C D) =
      ring.add S (ideal_quotient_lift h C) (ideal_quotient_lift h D)"
      by (simp add: C D FactRing_def J.a_rcos_sum[OF a b]
        quotient_lift_mk a b H.hom_add)
  qed
  show "ideal_quotient_lift h (monoid.one (FactRing R I)) = monoid.one S"
    by (simp add: FactRing_def quotient_lift_mk)
qed

lemma quotient_lift_unique:
  assumes agrees: "\<And>a. a \<in> carrier R \<Longrightarrow> g (a_r_coset R I a) = h a"
    and C: "C \<in> carrier (FactRing R I)"
  shows "g C = ideal_quotient_lift h C"
proof -
  obtain a where a: "a \<in> carrier R" and Ca: "C = a_r_coset R I a"
    using quotient_carrier_rep[OF C] by blast
  show ?thesis by (simp only: Ca agrees[OF a] quotient_lift_mk[OF a])
qed

end
end
