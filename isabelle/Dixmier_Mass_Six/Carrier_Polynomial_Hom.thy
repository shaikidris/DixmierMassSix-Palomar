theory Carrier_Polynomial_Hom
  imports "Mapped_Complex_Polynomial_Root"
    "Ideal_Quotient_Lift"
begin

abbreviation carrier_polynomial_ring :: "'a::field set \<Rightarrow> 'a list ring" where
  "carrier_polynomial_ring E \<equiv> univ_poly (nc_type_ring :: 'a ring) E"
definition mapped_polynomial_eval :: "('k::field \<Rightarrow> 'l::field) \<Rightarrow> 'l \<Rightarrow> 'k list \<Rightarrow> 'l" where
  "mapped_polynomial_eval f z p = ring.eval nc_type_ring (map f p) z"

lemma nc_type_ring_scalar_operations [simp]:
  "ring.zero (nc_type_ring :: 'a::ring_1 ring) = 0"
  "monoid.one (nc_type_ring :: 'a ring) = 1"
  "ring.add (nc_type_ring :: 'a ring) = (+)"
  "monoid.mult (nc_type_ring :: 'a ring) = (*)"
  by (simp_all add: nc_type_ring_def)

context dixmier_carrier_field_embedding
begin

interpretation source_record: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
interpretation target_record: field "nc_type_ring :: 'l ring" by (rule nc_type_ring_field)
interpretation coefficient_hom: ring_hom_ring "carrier_type_ring E" "nc_type_ring :: 'l ring" f
  by (rule carrier_embedding_ring_hom_ring)

lemma source_carrier_subfield: "subfield E (nc_type_ring :: 'k ring)"
  by (rule carrier_type_ring_subfield[OF carrier_closed])
lemma source_carrier_subring: "subring E (nc_type_ring :: 'k ring)"
  by (rule carrier_type_ring_subring[OF carrier_closed])
lemma target_UNIV_subring: "subring UNIV (nc_type_ring :: 'l ring)"
  using target_record.carrier_is_subring by (simp only: nc_type_ring_def ring_record_simps)
lemma source_polynomial_cring: "cring (carrier_polynomial_ring E)"
  by (rule source_record.univ_poly_is_cring[OF source_carrier_subring])
lemma source_polynomial_ring: "ring (carrier_polynomial_ring E)"
  by (rule source_record.univ_poly_is_ring[OF source_carrier_subring])
lemma target_polynomial_ring: "ring (carrier_polynomial_ring (UNIV::'l set))"
  by (rule target_record.univ_poly_is_ring[OF target_UNIV_subring])

lemma source_polynomial_coefficients:
  "p \<in> carrier (carrier_polynomial_ring E) \<Longrightarrow> set p \<subseteq> E"
  unfolding univ_poly_def polynomial_def by auto
lemma mapped_poly_add:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)"
    and q: "q \<in> carrier (carrier_polynomial_ring E)"
  shows "map f (ring.poly_add nc_type_ring p q) = ring.poly_add nc_type_ring (map f p) (map f q)"
proof -
  have pe: "set p \<subseteq> E" by (rule source_polynomial_coefficients[OF p])
  have qe: "set q \<subseteq> E" by (rule source_polynomial_coefficients[OF q])
  have pc: "set p \<subseteq> carrier (carrier_type_ring E)" using pe by simp
  have qc: "set q \<subseteq> carrier (carrier_type_ring E)" using qe by simp
  have consistent: "ring.poly_add (carrier_type_ring E) = ring.poly_add (nc_type_ring :: 'k ring)"
    unfolding carrier_type_ring_def by (rule source_record.poly_add_consistent[OF source_carrier_subring])
  have h: "ring.normalize (nc_type_ring :: 'l ring) (map f (ring.poly_add nc_type_ring p q)) =
    ring.poly_add nc_type_ring (map f p) (map f q)"
    using coefficient_hom.poly_add_hom'[OF pc qc] by (simp only: consistent)
  have out: "Polynomials.polynomial (nc_type_ring :: 'l ring) UNIV (map f (ring.poly_add nc_type_ring p q))"
    by (rule mapped_record_polynomial)
       (rule source_record.poly_add_is_polynomial[OF source_carrier_subring pe qe])
  show ?thesis using h by (simp only: target_record.normalize_polynomial[OF out])
qed
lemma mapped_poly_mult:
  assumes p: "p \<in> carrier (carrier_polynomial_ring E)"
    and q: "q \<in> carrier (carrier_polynomial_ring E)"
  shows "map f (ring.poly_mult nc_type_ring p q) = ring.poly_mult nc_type_ring (map f p) (map f q)"
proof -
  have pe: "set p \<subseteq> E" by (rule source_polynomial_coefficients[OF p])
  have qe: "set q \<subseteq> E" by (rule source_polynomial_coefficients[OF q])
  have pc: "set p \<subseteq> carrier (carrier_type_ring E)" using pe by simp
  have qc: "set q \<subseteq> carrier (carrier_type_ring E)" using qe by simp
  have consistent: "ring.poly_mult (carrier_type_ring E) = ring.poly_mult (nc_type_ring :: 'k ring)"
    unfolding carrier_type_ring_def by (rule source_record.poly_mult_consistent[OF source_carrier_subring])
  have h: "ring.normalize (nc_type_ring :: 'l ring) (map f (ring.poly_mult nc_type_ring p q)) =
    ring.poly_mult nc_type_ring (map f p) (map f q)"
    using coefficient_hom.poly_mult_hom'[OF pc qc] by (simp only: consistent)
  have out: "Polynomials.polynomial (nc_type_ring :: 'l ring) UNIV (map f (ring.poly_mult nc_type_ring p q))"
    by (rule mapped_record_polynomial)
       (rule source_record.poly_mult_is_polynomial[OF source_carrier_subring pe qe])
  show ?thesis using h by (simp only: target_record.normalize_polynomial[OF out])
qed

lemma mapped_polynomial_ring_hom:
  "map f \<in> ring_hom (carrier_polynomial_ring E) (carrier_polynomial_ring (UNIV::'l set))"
proof (rule ring_hom_memI)
  fix p assume p: "p \<in> carrier (carrier_polynomial_ring E)"
  have "Polynomials.polynomial (nc_type_ring :: 'k ring) E p" using p by (simp only: univ_poly_carrier)
  then have "Polynomials.polynomial (nc_type_ring :: 'l ring) UNIV (map f p)"
    by (rule mapped_record_polynomial)
  then show "map f p \<in> carrier (carrier_polynomial_ring (UNIV::'l set))"
    by (simp only: univ_poly_carrier)
next
  show "\<And>p q. p \<in> carrier (carrier_polynomial_ring E) \<Longrightarrow> q \<in> carrier (carrier_polynomial_ring E) \<Longrightarrow>
    map f (monoid.mult (carrier_polynomial_ring E) p q) =
    monoid.mult (carrier_polynomial_ring (UNIV::'l set)) (map f p) (map f q)"
    by (simp only: univ_poly_mult mapped_poly_mult)
next
  show "\<And>p q. p \<in> carrier (carrier_polynomial_ring E) \<Longrightarrow> q \<in> carrier (carrier_polynomial_ring E) \<Longrightarrow>
    map f (ring.add (carrier_polynomial_ring E) p q) =
    ring.add (carrier_polynomial_ring (UNIV::'l set)) (map f p) (map f q)"
    by (simp only: univ_poly_add mapped_poly_add)
next
  show "map f (monoid.one (carrier_polynomial_ring E)) = monoid.one (carrier_polynomial_ring (UNIV::'l set))"
    by (simp add: univ_poly_one nc_type_ring_def map_one)
qed

lemma mapped_polynomial_eval_hom:
  "mapped_polynomial_eval f z \<in> ring_hom (carrier_polynomial_ring E) (nc_type_ring :: 'l ring)"
proof -
  have zc: "z \<in> carrier (nc_type_ring :: 'l ring)" by (simp add: nc_type_ring_def)
  interpret ev: ring_hom_ring "carrier_polynomial_ring (UNIV::'l set)" "nc_type_ring :: 'l ring"
      "\<lambda>p. ring.eval (nc_type_ring :: 'l ring) p z"
    by (rule target_record.eval_ring_hom[OF target_UNIV_subring zc])
  show ?thesis
    using ring_hom_trans[OF mapped_polynomial_ring_hom ev.homh]
    by (simp only: comp_def mapped_polynomial_eval_def[abs_def])
qed
lemma mapped_polynomial_eval_hom_ring:
  "ring_hom_ring (carrier_polynomial_ring E) (nc_type_ring :: 'l ring) (mapped_polynomial_eval f z)"
  by (rule ring_hom_ringI2[OF source_polynomial_ring nc_type_ring_is_ring mapped_polynomial_eval_hom])

lemma source_polynomial_const_member:
  assumes c: "c \<in> E"
  shows "ring.poly_of_const (nc_type_ring :: 'k ring) c \<in> carrier (carrier_polynomial_ring E)"
proof -
  have h: "ring.poly_of_const (nc_type_ring :: 'k ring) \<in>
    ring_hom (carrier_type_ring E) (carrier_polynomial_ring E)"
    using source_record.canonical_embedding_is_hom[OF source_carrier_subring]
    by (simp only: carrier_type_ring_def)
  show ?thesis by (rule ring_hom_closed[OF h]) (simp only: carrier_type_ring_simps c)
qed
lemma mapped_polynomial_eval_const:
  assumes "c \<in> E"
  shows "mapped_polynomial_eval f z (ring.poly_of_const (nc_type_ring :: 'k ring) c) = f c"
proof -
  have zero: "ring.zero (nc_type_ring :: 'k ring) = 0" by (simp add: nc_type_ring_def)
  show ?thesis unfolding mapped_polynomial_eval_def source_record.poly_of_const_def
    by (cases "c=0") (simp_all add: source_record.normalize.simps zero nc_list_eval_poly)
qed
lemma source_polynomial_variable_member:
  "[1,0] \<in> carrier (carrier_polynomial_ring E)"
  by (simp add: univ_poly_def polynomial_def nc_type_ring_def)
lemma mapped_polynomial_eval_variable:
  "mapped_polynomial_eval f z [1,0] = z"
  by (simp add: mapped_polynomial_eval_def nc_list_eval_poly map_one)

end
end
