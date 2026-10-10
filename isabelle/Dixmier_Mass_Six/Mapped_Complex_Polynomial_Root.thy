theory Mapped_Complex_Polynomial_Root
  imports Carrier_List_Polynomials "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

text \<open>This result uses normalized nonconstancy, not mapped irreducibility.
No value of the embedding at an element outside E is constrained.\<close>
theorem mapped_nonconstant_complex_root:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex"
  assumes emb: "dixmier_carrier_field_embedding E f"
    and coeff: "set p \<subseteq> E"
    and normalized: "p=[] \<or> hd p \<noteq> 0"
    and positive_degree: "1 < length p"
  shows "\<exists>z::complex. ring.eval nc_type_ring (map f p) z = 0"
proof -
  interpret emb: dixmier_carrier_field_embedding E f by (rule emb)
  have deg: "0 < Polynomial.degree (Poly (rev (map f p)))"
    using positive_degree by (simp add: emb.mapped_list_poly_degree[OF coeff normalized])
  obtain z where root: "poly (Poly (rev (map f p))) z = 0"
    using alg_closed_imp_poly_has_root[OF deg] by blast
  have eval_zero: "ring.eval (nc_type_ring :: complex ring) (map f p) z = 0"
    by (simp only: nc_list_eval_poly root)
  show ?thesis by (rule exI[of _ z]) (rule eval_zero)
qed

corollary mapped_record_nonconstant_complex_root:
  fixes E :: "'k::field set" and f :: "'k \<Rightarrow> complex"
  assumes emb: "dixmier_carrier_field_embedding E f"
    and p: "Polynomials.polynomial (nc_type_ring :: 'k ring) E p"
    and degree: "1 < length p"
  shows "\<exists>z::complex. ring.eval nc_type_ring (map f p) z = 0"
proof -
  have coeff: "set p \<subseteq> E" and norm: "p=[] \<or> hd p \<noteq> 0"
    using p unfolding polynomial_def nc_type_ring_def by auto
  show ?thesis by (rule mapped_nonconstant_complex_root[OF emb coeff norm degree])
qed

end
