theory Carrier_Quotient_Root
  imports Carrier_Polynomial_Hom
begin

context dixmier_carrier_field_embedding
begin

lemma mapped_root_quotient_context:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)"
    and root: "mapped_polynomial_eval f z p = 0"
  shows "contained_ideal_quotient (carrier_polynomial_ring E) (nc_type_ring :: 'l ring)
    (mapped_polynomial_eval f z) (cgenideal (carrier_polynomial_ring E) p)"
proof -
  interpret U: cring "carrier_polynomial_ring E" by (rule source_polynomial_cring)
  interpret h: ring_hom_ring "carrier_polynomial_ring E" "nc_type_ring :: 'l ring" "mapped_polynomial_eval f z"
    by (rule mapped_polynomial_eval_hom_ring)
  have zero: "ring.zero (nc_type_ring :: 'l ring) = 0" by (simp add: nc_type_ring_def)
  have pi: "p \<in> a_kernel (carrier_polynomial_ring E) (nc_type_ring :: 'l ring) (mapped_polynomial_eval f z)"
    by (simp only: a_kernel_def' mem_Collect_eq p root zero simp_thms)
  have incl: "cgenideal (carrier_polynomial_ring E) p \<subseteq>
    a_kernel (carrier_polynomial_ring E) (nc_type_ring :: 'l ring) (mapped_polynomial_eval f z)"
    by (rule U.cgenideal_minimal[OF h.kernel_is_ideal pi])
  show ?thesis
    by (intro contained_ideal_quotient.intro mapped_polynomial_eval_hom_ring U.cgenideal_ideal[OF p]
        contained_ideal_quotient_axioms.intro incl)
qed

lemma mapped_root_quotient_hom:
  assumes "p \<in> carrier (carrier_polynomial_ring E)" "mapped_polynomial_eval f z p = 0"
  shows "ideal_quotient_lift (mapped_polynomial_eval f z) \<in>
    ring_hom (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)) (nc_type_ring :: 'l ring)"
  by (rule contained_ideal_quotient.quotient_lift_ring_hom[OF mapped_root_quotient_context[OF assms]])
lemma mapped_root_quotient_representative:
  assumes "p \<in> carrier (carrier_polynomial_ring E)" "mapped_polynomial_eval f z p = 0"
    "q \<in> carrier (carrier_polynomial_ring E)"
  shows "ideal_quotient_lift (mapped_polynomial_eval f z)
    (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) q) = mapped_polynomial_eval f z q"
  by (rule contained_ideal_quotient.quotient_lift_mk[OF mapped_root_quotient_context[OF assms(1,2)] assms(3)])

lemma source_irreducible_quotient_field:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)"
    and irreducible: "Ring_Divisibility.ring_irreducible (carrier_polynomial_ring E) p"
  shows "field (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p))"
  using domain.rupture_is_field_iff_pirreducible[OF field.axioms(1)[OF nc_type_ring_field] source_carrier_subfield p] irreducible
  by (simp only: rupture_def)
lemma mapped_root_quotient_injective:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)"
    and root: "mapped_polynomial_eval f z p = 0"
    and irreducible: "Ring_Divisibility.ring_irreducible (carrier_polynomial_ring E) p"
  shows "inj_on (ideal_quotient_lift (mapped_polynomial_eval f z))
    (carrier (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)))"
  by (rule non_trivial_field_hom_is_inj[OF mapped_root_quotient_hom[OF p root]
      source_irreducible_quotient_field[OF p irreducible] nc_type_ring_field])

lemma mapped_root_quotient_const:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)" and root: "mapped_polynomial_eval f z p = 0"
    and c: "c \<in> E"
  shows "ideal_quotient_lift (mapped_polynomial_eval f z)
    (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)
      (ring.poly_of_const (nc_type_ring :: 'k ring) c)) = f c"
  by (simp only: mapped_root_quotient_representative[OF p root source_polynomial_const_member[OF c]]
      mapped_polynomial_eval_const[OF c])
lemma mapped_root_quotient_variable:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)" and root: "mapped_polynomial_eval f z p = 0"
  shows "ideal_quotient_lift (mapped_polynomial_eval f z)
    (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) [1,0]) = z"
  by (simp only: mapped_root_quotient_representative[OF p root source_polynomial_variable_member]
      mapped_polynomial_eval_variable)

end

text \<open>Source irreducibility supplies a field quotient and positive degree.
The mapped polynomial only needs a root; its irreducibility is never required.\<close>
theorem exists_complex_polynomial_quotient_embedding:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and p :: "'k list"
  assumes emb: "dixmier_carrier_field_embedding E f"
    and p: "p \<in> carrier (carrier_polynomial_ring E)"
    and irreducible: "Ring_Divisibility.ring_irreducible (carrier_polynomial_ring E) p"
  shows "\<exists>z::complex. \<exists>H::'k list set \<Rightarrow> complex.
    H \<in> ring_hom (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)) nc_type_ring \<and>
    inj_on H (carrier (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p))) \<and>
    (\<forall>q\<in>carrier (carrier_polynomial_ring E).
      H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) q) = mapped_polynomial_eval f z q) \<and>
    (\<forall>c\<in>E. H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)
      (ring.poly_of_const nc_type_ring c)) = f c) \<and>
    H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) [1,0]) = z"
proof -
  interpret emb: dixmier_carrier_field_embedding E f by (rule emb)
  have degree: "1 < length p"
    using ring.pirreducible_degree[OF nc_type_ring_is_ring emb.source_carrier_subfield p irreducible] by arith
  have poly: "Polynomials.polynomial (nc_type_ring :: 'k ring) E p" using p by (simp only: univ_poly_carrier)
  obtain z where z: "ring.eval (nc_type_ring :: complex ring) (map f p) z = 0"
    using mapped_record_nonconstant_complex_root[OF emb poly degree] by blast
  have root: "mapped_polynomial_eval f z p = 0" using z by (simp only: mapped_polynomial_eval_def)
  let ?H = "ideal_quotient_lift (mapped_polynomial_eval f z)"
  show ?thesis
  proof (rule exI[of _ z], rule exI[of _ ?H], intro conjI)
    show "?H \<in> ring_hom (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)) nc_type_ring"
      by (rule emb.mapped_root_quotient_hom[OF p root])
    show "inj_on ?H (carrier (FactRing (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)))"
      by (rule emb.mapped_root_quotient_injective[OF p root irreducible])
    show "\<forall>q\<in>carrier (carrier_polynomial_ring E).
      ?H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) q) = mapped_polynomial_eval f z q"
      by (intro ballI emb.mapped_root_quotient_representative[OF p root])
    show "\<forall>c\<in>E. ?H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p)
      (ring.poly_of_const nc_type_ring c)) = f c"
      by (intro ballI emb.mapped_root_quotient_const[OF p root])
    show "?H (a_r_coset (carrier_polynomial_ring E) (cgenideal (carrier_polynomial_ring E) p) [1,0]) = z"
      by (rule emb.mapped_root_quotient_variable[OF p root])
  qed
qed

end
