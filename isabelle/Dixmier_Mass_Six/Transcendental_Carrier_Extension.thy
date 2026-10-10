theory Transcendental_Carrier_Extension
  imports Carrier_Subring_Transport
begin

text \<open>The polynomial-value carrier is only a subring in this branch.
Injective transport is proved directly; the reviewed fraction extension then
passes to its division closure.\<close>
theorem transcendental_carrier_extension_with_representatives:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and a :: 'k
  assumes emb: "dixmier_carrier_field_embedding E f"
    and count: "countable E"
    and trans: "ring.transcendental (nc_type_ring :: 'k ring) E a"
  shows "\<exists>z::complex. \<exists>g::'k \<Rightarrow> complex.
    dixmier_carrier_field_embedding (division_closure (insert a E)) g \<and>
    (\<forall>c\<in>E. g c=f c) \<and> g a=z \<and>
    (\<forall>q\<in>carrier (carrier_polynomial_ring E).
      g (ring.eval (nc_type_ring :: 'k ring) q a) = mapped_polynomial_eval f z q)"
proof -
  interpret emb: dixmier_carrier_field_embedding E f by (rule emb)
  interpret K: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
  let ?U = "carrier_polynomial_ring E"
  let ?A = "ring.simple_extension (nc_type_ring :: 'k ring) E a"
  let ?ev = "\<lambda>q. ring.eval (nc_type_ring :: 'k ring) q a"
  have sr: "subring E (nc_type_ring :: 'k ring)" by (rule emb.source_carrier_subring)
  have ec: "E \<subseteq> carrier (nc_type_ring :: 'k ring)" by (rule subringE(1)[OF sr])
  have ac: "a \<in> carrier (nc_type_ring :: 'k ring)" by (simp add: nc_type_ring_def)
  have asr: "subring ?A (nc_type_ring :: 'k ring)" by (rule K.simple_extension_is_subring[OF sr ac])
  have ea: "E \<subseteq> ?A" by (rule K.simple_extension_incl[OF ec ac])
  have aa: "a \<in> ?A" by (rule K.simple_extension_mem[OF sr ac])
  have img: "?A = ?ev ` carrier ?U" by (rule K.simple_extension_as_eval_img[OF ec ac])
  interpret ev: ring_hom_ring ?U "nc_type_ring :: 'k ring" ?ev by (rule K.eval_ring_hom[OF sr ac])
  have einj: "inj_on ?ev (carrier ?U)" using trans by (simp only: K.transcendental_def)
  have iso: "?ev \<in> ring_iso ?U (carrier_type_ring ?A)"
    using injective_ring_hom_image_iso[OF ev.homh einj]
    by (simp only: img[symmetric] carrier_type_ring_def)
  obtain z where zinj: "inj_on (mapped_polynomial_eval f z) (carrier ?U)"
    using exists_injective_mapped_polynomial_evaluation[OF emb count] by blast
  let ?h = "mapped_polynomial_eval f z \<circ> inv_into (carrier ?U) ?ev"
  have hr: "dixmier_carrier_ring_embedding ?A ?h"
    by (rule injective_iso_transport_ring_embedding[OF emb.source_polynomial_ring asr iso
        emb.mapped_polynomial_eval_hom zinj])
  interpret h: dixmier_carrier_ring_embedding ?A ?h by (rule hr)
  have hrep: "?h (?ev q)=mapped_polynomial_eval f z q" if "q \<in> carrier ?U" for q
    by (rule quotient_iso_transport_representative[OF iso that])
  obtain g :: "'k \<Rightarrow> complex" where ge: "dixmier_carrier_field_embedding (division_closure ?A) g"
    and agreesA: "\<forall>x\<in>?A. g x=?h x"
    using h.exists_fraction_extension by blast
  have closure: "division_closure ?A = division_closure (insert a E)"
    by (rule simple_extension_division_closure[OF emb.carrier_closed])
  have gc: "dixmier_carrier_field_embedding (division_closure (insert a E)) g"
    using ge by (simp only: closure)
  have rep: "g (?ev q)=mapped_polynomial_eval f z q" if qm: "q \<in> carrier ?U" for q
  proof -
    have qa: "?ev q \<in> ?A" unfolding img by (rule imageI[OF qm])
    have "g (?ev q)=?h (?ev q)" by (rule agreesA[rule_format, OF qa])
    also have "...=mapped_polynomial_eval f z q" by (rule hrep[OF qm])
    finally show ?thesis .
  qed
  have agrees: "g c=f c" if ce: "c \<in> E" for c
  proof -
    have cm: "ring.poly_of_const (nc_type_ring :: 'k ring) c \<in> carrier ?U"
      by (rule emb.source_polynomial_const_member[OF ce])
    have "g c=g (?ev (ring.poly_of_const (nc_type_ring :: 'k ring) c))" by (simp only: nc_list_eval_const)
    also have "...=mapped_polynomial_eval f z (ring.poly_of_const (nc_type_ring :: 'k ring) c)" by (rule rep[OF cm])
    also have "...=f c" by (rule emb.mapped_polynomial_eval_const[OF ce])
    finally show ?thesis .
  qed
  have generator: "g a=z"
  proof -
    have "g a=g (?ev [1,0])" by (simp only: nc_list_eval_variable)
    also have "...=mapped_polynomial_eval f z [1,0]" by (rule rep[OF emb.source_polynomial_variable_member])
    also have "...=z" by (rule emb.mapped_polynomial_eval_variable)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule exI[of _ z], rule exI[of _ g], intro conjI)
    show "dixmier_carrier_field_embedding (division_closure (insert a E)) g" by (rule gc)
    show "\<forall>c\<in>E. g c=f c" by (intro ballI agrees)
    show "g a=z" by (rule generator)
    show "\<forall>q\<in>carrier ?U. g (?ev q)=mapped_polynomial_eval f z q" by (intro ballI rep)
  qed
qed

corollary transcendental_carrier_embedding_extension:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and a :: 'k
  assumes "dixmier_carrier_field_embedding E f" "countable E"
    "ring.transcendental (nc_type_ring :: 'k ring) E a"
  shows "\<exists>g::'k \<Rightarrow> complex. dixmier_carrier_field_embedding (division_closure (insert a E)) g \<and>
    (\<forall>c\<in>E. g c=f c)"
  using transcendental_carrier_extension_with_representatives[OF assms] by blast

theorem countable_carrier_one_generator_extension:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex" and a :: 'k
  assumes emb: "dixmier_carrier_field_embedding E f" and count: "countable E"
  shows "\<exists>g::'k \<Rightarrow> complex. dixmier_carrier_field_embedding (division_closure (insert a E)) g \<and>
    (\<forall>c\<in>E. g c=f c)"
proof (cases "ring.transcendental (nc_type_ring :: 'k ring) E a")
  case True show ?thesis by (rule transcendental_carrier_embedding_extension[OF emb count True])
next
  case False show ?thesis by (rule algebraic_carrier_embedding_extension[OF emb False])
qed

end
