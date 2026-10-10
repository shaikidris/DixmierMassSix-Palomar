theory Carrier_Transcendental_Point
  imports "Algebraic_Carrier_Extension"
    "Countable_Complex_Root_Avoidance"
begin

theorem exists_injective_mapped_polynomial_evaluation:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex"
  assumes emb: "dixmier_carrier_field_embedding E f" and count: "countable E"
  shows "\<exists>z::complex.
    (\<forall>q\<in>carrier (carrier_polynomial_ring E). q \<noteq> [] \<longrightarrow> mapped_polynomial_eval f z q \<noteq> 0) \<and>
    inj_on (mapped_polynomial_eval f z) (carrier (carrier_polynomial_ring E))"
proof -
  interpret emb: dixmier_carrier_field_embedding E f by (rule emb)
  have image_count: "countable (f ` E)" using count by simp
  obtain z where avoid: "\<forall>p::complex poly. p \<noteq> 0 \<longrightarrow> set (coeffs p) \<subseteq> f ` E \<longrightarrow> poly p z \<noteq> 0"
    using exists_complex_avoiding_countable_coefficients[OF image_count] by blast
  have nonzero: "mapped_polynomial_eval f z q \<noteq> 0"
    if qm: "q \<in> carrier (carrier_polynomial_ring E)" and qnz: "q \<noteq> []" for q
  proof -
    have coeff: "set q \<subseteq> E" by (rule emb.source_polynomial_coefficients[OF qm])
    have normal: "q=[] \<or> hd q \<noteq> 0"
      using qm by (auto simp: univ_poly_def polynomial_def)
    have mapped_normal: "map f q=[] \<or> hd (map f q) \<noteq> 0"
      by (rule emb.mapped_list_normalized[OF coeff normal])
    have mapped_nonempty: "map f q \<noteq> []" using qnz by simp
    have pnz: "Poly (rev (map f q)) \<noteq> 0"
      by (rule Poly_rev_normalized_nonzero[OF mapped_normal mapped_nonempty])
    have cs: "set (coeffs (Poly (rev (map f q)))) \<subseteq> f ` E"
      by (simp only: coeffs_Poly_rev_normalized[OF mapped_normal] set_rev set_map)
         (rule image_mono[OF coeff])
    have "poly (Poly (rev (map f q))) z \<noteq> 0" by (rule avoid[rule_format, OF pnz cs])
    then show ?thesis by (simp only: mapped_polynomial_eval_def nc_list_eval_poly simp_thms)
  qed
  let ?U = "carrier_polynomial_ring E"
  let ?h = "mapped_polynomial_eval f z"
  interpret ev: ring_hom_ring ?U "nc_type_ring :: complex ring" ?h
    by (rule emb.mapped_polynomial_eval_hom_ring)
  have hzero: "?h []=0" by (simp add: mapped_polynomial_eval_def nc_list_eval_poly)
  have empty_member: "[] \<in> carrier ?U" by (rule univ_poly_zero_closed)
  have kernel: "a_kernel ?U (nc_type_ring :: complex ring) ?h = {[]}"
  proof (rule Set.set_eqI, rule iffI)
    fix q :: "'k list" assume qk: "q \<in> a_kernel ?U (nc_type_ring :: complex ring) ?h"
    have props: "q \<in> carrier ?U \<and> ?h q=0"
      using qk by (simp only: a_kernel_def' mem_Collect_eq nc_type_ring_scalar_operations)
    have qm: "q \<in> carrier ?U" by (rule conjunct1[OF props])
    have qzero: "?h q=0" by (rule conjunct2[OF props])
    have "q=[]" using nonzero[OF qm] qzero by blast
    then show "q \<in> {[]}" by simp
  next
    fix q :: "'k list" assume "q \<in> {[]}"
    then have "q=[]" by simp
    then show "q \<in> a_kernel ?U (nc_type_ring :: complex ring) ?h"
      by (simp only: a_kernel_def' mem_Collect_eq empty_member hzero nc_type_ring_scalar_operations simp_thms)
  qed
  have inj: "inj_on ?h (carrier ?U)"
    by (rule ev.trivial_ker_imp_inj) (simp only: kernel univ_poly_zero)
  show ?thesis
  proof (rule exI[of _ z], intro conjI)
    show "\<forall>q\<in>carrier ?U. q \<noteq> [] \<longrightarrow> ?h q \<noteq> 0"
    proof (intro ballI impI)
      fix q :: "'k list" assume qm: "q \<in> carrier ?U" and qnz: "q \<noteq> []"
      show "?h q \<noteq> 0" by (rule nonzero[OF qm qnz])
    qed
    show "inj_on ?h (carrier ?U)" by (rule inj)
  qed
qed

end
