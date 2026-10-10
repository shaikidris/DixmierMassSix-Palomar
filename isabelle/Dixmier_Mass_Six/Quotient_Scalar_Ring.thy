theory Quotient_Scalar_Ring
  imports Central_Scalar_Ring
begin

text \<open>These carrier facts are derived directly from the quotient projection
and coset definition. They avoid an unnecessary dependency on the concrete
evaluation locale when proving relation-only normal spanning.\<close>

lemma quotient_projection_closed:
  "abstract_mk f \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (rule ring_hom_closed[OF abstract_mk_ring_hom])
     (simp only: free_ring_simps UNIV_I)
lemma quotient_representative:
  assumes "z \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  shows "\<exists>f. z = abstract_mk f"
  using assms by (auto simp: abstract_weyl_ring_def FactRing_def A_RCOSETS_def' abstract_mk_def)
lemma quotient_X_closed:
  "abstract_X \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp only: abstract_X_def quotient_projection_closed)
lemma quotient_Y_closed:
  "abstract_Y \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp only: abstract_Y_def quotient_projection_closed)
lemma quotient_scalar_closed:
  "abstract_scalar c \<in> carrier abstract_weyl_ring"
  by (simp only: abstract_scalar_def quotient_projection_closed)
lemma quotient_scalar_central:
  assumes "z \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  shows "monoid.mult abstract_weyl_ring (abstract_scalar c) z =
    monoid.mult abstract_weyl_ring z (abstract_scalar c)"
proof -
  obtain f where z: "z = abstract_mk f" using quotient_representative[OF assms] by blast
  show ?thesis by (simp only: z abstract_scalar_def abstract_mk_mult[symmetric] free_scalar_central)
qed

lemma abstract_scalar_zero:
  "abstract_scalar 0 = ring.zero (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp only: abstract_scalar_def free_scalar_zero abstract_mk_zero)
lemma abstract_scalar_one:
  "abstract_scalar 1 = monoid.one (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp only: abstract_scalar_def free_scalar_one abstract_mk_one)
lemma abstract_scalar_add:
  "abstract_scalar (a+b) = ring.add abstract_weyl_ring (abstract_scalar a) (abstract_scalar b)"
  by (simp only: abstract_scalar_def free_scalar_add abstract_mk_add)
lemma abstract_scalar_mult:
  "abstract_scalar (a*b) = monoid.mult abstract_weyl_ring (abstract_scalar a) (abstract_scalar b)"
  by (simp only: abstract_scalar_def free_scalar_mult abstract_mk_mult)

lemma abstract_scalar_hom:
  "abstract_scalar \<in> ring_hom (nc_type_ring :: 'k::field ring) abstract_weyl_ring"
proof (rule ring_hom_memI)
  show "\<And>x. x \<in> carrier (nc_type_ring :: 'k ring) \<Longrightarrow> abstract_scalar x \<in> carrier abstract_weyl_ring"
    by (rule quotient_scalar_closed)
  show "\<And>x y. x \<in> carrier (nc_type_ring :: 'k ring) \<Longrightarrow> y \<in> carrier nc_type_ring \<Longrightarrow>
    abstract_scalar (monoid.mult nc_type_ring x y) =
    monoid.mult abstract_weyl_ring (abstract_scalar x) (abstract_scalar y)"
    by (simp only: nc_type_ring_def ring_record_simps abstract_scalar_mult)
  show "\<And>x y. x \<in> carrier (nc_type_ring :: 'k ring) \<Longrightarrow> y \<in> carrier nc_type_ring \<Longrightarrow>
    abstract_scalar (ring.add nc_type_ring x y) =
    ring.add abstract_weyl_ring (abstract_scalar x) (abstract_scalar y)"
    by (simp only: nc_type_ring_def ring_record_simps abstract_scalar_add)
  show "abstract_scalar (monoid.one (nc_type_ring :: 'k ring)) = monoid.one abstract_weyl_ring"
    by (simp only: nc_type_ring_def ring_record_simps abstract_scalar_one)
qed

lemma abstract_central_scalar_ring:
  "central_scalar_ring (abstract_weyl_ring :: 'k::field weyl_free set ring) abstract_scalar"
proof -
  have hom: "ring_hom_ring (nc_type_ring :: 'k ring) abstract_weyl_ring abstract_scalar"
    by (rule ring_hom_ringI2[OF nc_type_ring_is_ring abstract_weyl_ring_is_ring abstract_scalar_hom])
  show ?thesis
    by (rule central_scalar_ring.intro[OF hom]; rule central_scalar_ring_axioms.intro)
       (rule quotient_scalar_central)
qed

end
