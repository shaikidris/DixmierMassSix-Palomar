theory Algebraic_Carrier_Extension
  imports Carrier_Record_Converse
begin

lemma algebraic_simple_extension_division_closure:
  fixes E :: "'k::field set" and a :: 'k
  assumes closed: "division_subring_on E"
    and alg: "\<not> ring.transcendental (nc_type_ring :: 'k ring) E a"
  shows "ring.simple_extension (nc_type_ring :: 'k ring) E a = division_closure (insert a E)"
proof -
  interpret K: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
  let ?A = "ring.simple_extension (nc_type_ring :: 'k ring) E a"
  let ?D = "division_closure (insert a E)"
  have sf: "subfield E (nc_type_ring :: 'k ring)" by (rule carrier_type_ring_subfield[OF closed])
  have sr: "subring E (nc_type_ring :: 'k ring)" by (rule subfieldE(1)[OF sf])
  have ac: "a \<in> carrier (nc_type_ring :: 'k ring)" by (simp add: nc_type_ring_def)
  have asf: "subfield ?A (nc_type_ring :: 'k ring)"
    using K.simple_extension_is_subfield[unfolded over_def, OF sf ac] alg by blast
  have aclosed: "division_subring_on ?A" by (rule subfield_division_subring_on[OF asf])
  have ea: "E \<subseteq> ?A" by (rule K.simple_extension_incl[OF subfieldE(3)[OF sf] ac])
  have aa: "a \<in> ?A" by (rule K.simple_extension_mem[OF sr ac])
  have da: "?D \<subseteq> ?A" by (rule division_closure_least[OF aclosed]) (use ea aa in auto)
  have dclosed: "division_subring_on ?D" by (rule division_closure_is_division_subring)
  have dsr: "subring ?D (nc_type_ring :: 'k ring)" by (rule carrier_type_ring_subring[OF dclosed])
  have ed: "E \<subseteq> ?D" using division_closure_contains[of "insert a E"] by blast
  have ad: "a \<in> ?D" by (rule division_closure_generator) simp
  have "?A \<subseteq> ?D" by (rule K.simple_extension_subring_incl[OF dsr ed ad])
  then show ?thesis by (rule subset_antisym[OF _ da])
qed

lemma nc_list_eval_const:
  "ring.eval (nc_type_ring :: 'k::field ring) (ring.poly_of_const nc_type_ring c) a = c"
proof -
  interpret K: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
  show ?thesis unfolding K.poly_of_const_def
    by (cases "c=0") (simp_all add: K.normalize.simps nc_list_eval_poly)
qed
lemma nc_list_eval_variable:
  "ring.eval (nc_type_ring :: 'k::field ring) [1,0] a = a"
  by (simp add: nc_list_eval_poly)

text \<open>The explicit source evaluation isomorphism is retained. Its inverse
is composed with the quotient-root embedding, so agreement on coefficients is
proved rather than inferred from an anonymous field isomorphism.\<close>
theorem algebraic_carrier_extension_with_representatives:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and a :: 'k
  assumes emb: "dixmier_carrier_field_embedding E f"
    and alg: "\<not> ring.transcendental (nc_type_ring :: 'k ring) E a"
  shows "\<exists>z::complex. \<exists>g::'k \<Rightarrow> complex.
    dixmier_carrier_field_embedding (division_closure (insert a E)) g \<and>
    (\<forall>c\<in>E. g c = f c) \<and> g a = z \<and>
    (\<forall>q\<in>carrier (carrier_polynomial_ring E).
      g (ring.eval (nc_type_ring :: 'k ring) q a) = mapped_polynomial_eval f z q)"
proof -
  interpret emb: dixmier_carrier_field_embedding E f by (rule emb)
  interpret K: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
  let ?U = "carrier_polynomial_ring E"
  let ?p = "ring.Irr (nc_type_ring :: 'k ring) E a"
  let ?I = "cgenideal ?U ?p"
  let ?Q = "FactRing ?U ?I"
  let ?A = "ring.simple_extension (nc_type_ring :: 'k ring) E a"
  let ?ev = "\<lambda>q. ring.eval (nc_type_ring :: 'k ring) q a"
  let ?e = "\<lambda>C. the_elem (?ev ` C)"
  have sf: "subfield E (nc_type_ring :: 'k ring)" by (rule emb.source_carrier_subfield)
  have sr: "subring E (nc_type_ring :: 'k ring)" by (rule subfieldE(1)[OF sf])
  have ac: "a \<in> carrier (nc_type_ring :: 'k ring)" by (simp add: nc_type_ring_def)
  have pm: "?p \<in> carrier ?U" by (rule K.IrrE(1)[unfolded over_def, OF sf ac alg])
  have irr: "Ring_Divisibility.ring_irreducible ?U ?p" by (rule K.IrrE(2)[unfolded over_def, OF sf ac alg])
  have ker: "a_kernel ?U (nc_type_ring :: 'k ring) ?ev = ?I"
    by (rule K.Irr_generates_ker[unfolded over_def, OF sf ac alg])
  interpret ev: ring_hom_ring ?U "nc_type_ring :: 'k ring" ?ev
    by (rule K.eval_ring_hom[OF sr ac])
  have img: "?A = ?ev ` carrier ?U"
    by (rule K.simple_extension_as_eval_img[OF subfieldE(3)[OF sf] ac])
  have iso: "?e \<in> ring_iso ?Q (carrier_type_ring ?A)"
    using ev.FactRing_iso_set_aux
    by (simp only: ker img[symmetric] carrier_type_ring_def)
  have erep: "?e (a_r_coset ?U ?I q) = ?ev q" if "q \<in> carrier ?U" for q
    using ev.the_elem_simp[OF that] by (simp only: ker)
  have qfield: "field ?Q" by (rule emb.source_irreducible_quotient_field[OF pm irr])
  have qr: "ring ?Q" by (rule field.is_ring[OF qfield])
  have acl: "division_subring_on ?A"
    using K.simple_extension_is_subfield[unfolded over_def, OF sf ac] alg
    by (intro subfield_division_subring_on) blast
  have closure: "?A = division_closure (insert a E)"
    by (rule algebraic_simple_extension_division_closure[OF emb.carrier_closed alg])
  obtain z :: complex and H :: "'k list set \<Rightarrow> complex" where
    hh: "H \<in> ring_hom ?Q (nc_type_ring :: complex ring)"
    and hrep: "\<forall>q\<in>carrier ?U. H (a_r_coset ?U ?I q) = mapped_polynomial_eval f z q"
    using exists_complex_polynomial_quotient_embedding[OF emb pm irr] by blast
  let ?g = "H \<circ> inv_into (carrier ?Q) ?e"
  have ga: "dixmier_carrier_field_embedding ?A ?g"
    by (rule quotient_iso_transport_embedding[OF qr acl iso hh])
  have gc: "dixmier_carrier_field_embedding (division_closure (insert a E)) ?g"
    using ga by (simp only: closure)
  have representative: "?g (?ev q) = mapped_polynomial_eval f z q" if qm: "q \<in> carrier ?U" for q
  proof -
    have coset: "a_r_coset ?U ?I q \<in> carrier ?Q"
      using qm by (auto simp: FactRing_def A_RCOSETS_def')
    have "?g (?ev q) = ?g (?e (a_r_coset ?U ?I q))" by (simp only: erep[OF qm])
    also have "... = H (a_r_coset ?U ?I q)" by (rule quotient_iso_transport_representative[OF iso coset])
    also have "... = mapped_polynomial_eval f z q" by (rule hrep[rule_format, OF qm])
    finally show ?thesis .
  qed
  have agrees: "?g c = f c" if ce: "c \<in> E" for c
  proof -
    have cm: "ring.poly_of_const (nc_type_ring :: 'k ring) c \<in> carrier ?U"
      by (rule emb.source_polynomial_const_member[OF ce])
    have "?g c = ?g (?ev (ring.poly_of_const (nc_type_ring :: 'k ring) c))"
      by (simp only: nc_list_eval_const)
    also have "... = mapped_polynomial_eval f z (ring.poly_of_const (nc_type_ring :: 'k ring) c)"
      by (rule representative[OF cm])
    also have "... = f c" by (rule emb.mapped_polynomial_eval_const[OF ce])
    finally show ?thesis .
  qed
  have generator: "?g a = z"
  proof -
    have "?g a = ?g (?ev [1,0])" by (simp only: nc_list_eval_variable)
    also have "... = mapped_polynomial_eval f z [1,0]" by (rule representative[OF emb.source_polynomial_variable_member])
    also have "... = z" by (rule emb.mapped_polynomial_eval_variable)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule exI[of _ z], rule exI[of _ ?g], intro conjI)
    show "dixmier_carrier_field_embedding (division_closure (insert a E)) ?g" by (rule gc)
    show "\<forall>c\<in>E. ?g c = f c" by (intro ballI agrees)
    show "?g a=z" by (rule generator)
    show "\<forall>q\<in>carrier ?U. ?g (?ev q) = mapped_polynomial_eval f z q"
      by (intro ballI representative)
  qed
qed

corollary algebraic_carrier_embedding_extension:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and a :: 'k
  assumes "dixmier_carrier_field_embedding E f"
    "\<not> ring.transcendental (nc_type_ring :: 'k ring) E a"
  shows "\<exists>g::'k \<Rightarrow> complex. dixmier_carrier_field_embedding (division_closure (insert a E)) g \<and>
    (\<forall>c\<in>E. g c = f c)"
  using algebraic_carrier_extension_with_representatives[OF assms] by blast

end
