theory Carrier_List_Polynomials
  imports "Carrier_Field_Records"
    "HOL-Algebra.Finite_Extensions"
begin

lemma carrier_type_ring_subfield:
  assumes closed: "division_subring_on S"
  shows "subfield S (nc_type_ring :: 'a::field ring)"
proof -
  interpret K: field "nc_type_ring :: 'a ring" by (rule nc_type_ring_field)
  show ?thesis
  proof (rule K.subfield_iff(1))
    show "field ((nc_type_ring :: 'a ring) \<lparr>carrier := S\<rparr>)"
      using carrier_type_ring_field[OF closed] unfolding carrier_type_ring_def .
    show "S \<subseteq> carrier (nc_type_ring :: 'a ring)" by (simp add: nc_type_ring_def)
  qed
qed
lemma carrier_type_ring_subring:
  "division_subring_on S \<Longrightarrow> subring S (nc_type_ring :: 'a::field ring)"
  by (rule subfieldE(1)[OF carrier_type_ring_subfield])

lemma nc_type_ring_nat_pow:
  "pow (nc_type_ring :: 'a::field ring) a (n::nat) = a^n"
  by (induction n) (simp_all add: nc_type_ring_def power_Suc2)

text \<open>HOL-Algebra lists put the leading coefficient first. Class Poly
expects the constant coefficient first, so reversal is essential.\<close>
lemma nc_list_eval_poly:
  "ring.eval (nc_type_ring :: 'a::field ring) p x = poly (Poly (rev p)) x"
proof -
  interpret K: field "nc_type_ring :: 'a ring" by (rule nc_type_ring_field)
  have zero: "ring.zero (nc_type_ring :: 'a ring) = 0" by (simp add: nc_type_ring_def)
  have add: "ring.add (nc_type_ring :: 'a ring) = (+)" by (simp add: nc_type_ring_def)
  have mult: "monoid.mult (nc_type_ring :: 'a ring) = (*)" by (simp add: nc_type_ring_def)
  show ?thesis
    by (induction p) (simp_all add: K.eval.simps nc_type_ring_nat_pow zero add mult Poly_append poly_monom add.commute)
qed

lemma carrier_list_eval_poly:
  fixes S :: "'a::field set" and p :: "'a list" and x :: 'a
  assumes closed: "division_subring_on S"
  shows "ring.eval (carrier_type_ring S) p x = poly (Poly (rev p)) x"
proof -
  interpret K: field "nc_type_ring :: 'a::field ring" by (rule nc_type_ring_field)
  have eq: "ring.eval (carrier_type_ring S) = ring.eval (nc_type_ring :: 'a ring)"
    unfolding carrier_type_ring_def
    by (rule K.eval_consistent[OF carrier_type_ring_subring[OF closed]])
  show ?thesis by (simp only: eq nc_list_eval_poly)
qed

lemma coeffs_Poly_rev_normalized:
  assumes normalized: "p=[] \<or> hd p \<noteq> (0::'a::zero)"
  shows "Polynomial.coeffs (Poly (rev p)) = rev p"
proof -
  have nt: "no_trailing (HOL.eq 0) (rev p)"
    using normalized by (cases p) (auto simp: no_trailing_unfold)
  show ?thesis by (simp only: coeffs_Poly strip_while_idem[OF nt])
qed
lemma degree_Poly_rev_normalized:
  assumes "p=[] \<or> hd p \<noteq> (0::'a::zero)"
  shows "Polynomial.degree (Poly (rev p)) = length p - 1"
  by (simp only: Polynomial.degree_eq_length_coeffs coeffs_Poly_rev_normalized[OF assms] length_rev)
lemma Poly_rev_normalized_nonzero:
  assumes "p=[] \<or> hd p \<noteq> (0::'a::zero)" "p \<noteq> []"
  shows "Poly (rev p) \<noteq> 0"
proof
  assume z: "Poly (rev p) = 0"
  have "[] = rev p"
    using coeffs_Poly_rev_normalized[OF assms(1)] by (simp only: z coeffs_0_eq_Nil)
  then have "p=[]" by simp
  then show False using assms(2) by contradiction
qed

context dixmier_carrier_field_embedding
begin
lemma mapped_list_normalized:
  assumes coeff: "set p \<subseteq> E" and normalized: "p=[] \<or> hd p \<noteq> 0"
  shows "map f p=[] \<or> hd (map f p) \<noteq> 0"
proof (cases p)
  case Nil then show ?thesis by simp
next
  case (Cons a ps)
  have ae: "a \<in> E" using coeff Cons by simp
  have an: "a \<noteq> 0" using normalized Cons by simp
  have fn: "f a \<noteq> 0" using map_eq_zero_on[OF ae] an by simp
  show ?thesis using fn Cons by simp
qed
lemma mapped_list_poly_degree:
  assumes "set p \<subseteq> E" "p=[] \<or> hd p \<noteq> 0"
  shows "Polynomial.degree (Poly (rev (map f p))) = length p - 1"
  using degree_Poly_rev_normalized[OF mapped_list_normalized[OF assms]] by simp
lemma mapped_record_polynomial:
  assumes "Polynomials.polynomial (nc_type_ring :: 'k ring) E p"
  shows "Polynomials.polynomial (nc_type_ring :: 'l ring) UNIV (map f p)"
proof -
  have coeff: "set p \<subseteq> E" and norm: "p=[] \<or> hd p \<noteq> 0"
    using assms unfolding polynomial_def nc_type_ring_def by auto
  show ?thesis using mapped_list_normalized[OF coeff norm]
    unfolding polynomial_def nc_type_ring_def by auto
qed
end

end
