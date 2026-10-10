theory Weyl_Leading_Forms
  imports Weighted_Contraction_Bounds
begin

lemma symbol_mul_bound_and_top:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
  shows "weighted_degree rho sigma (pbw_symbol (op_comp P Q)) \<le> bot.Value (m+n)"
    and "weighted_component rho sigma (m+n) (pbw_symbol (op_comp P Q)) =
      weighted_component rho sigma m (pbw_symbol P)*weighted_component rho sigma n (pbw_symbol Q)"
proof -
  obtain S T c d where fs: "finite S" and ft: "finite T" and pc: "finite_normal_sum S c=P"
    and qc: "finite_normal_sum T d=Q" and cb: "\<forall>u\<in>S. pair_weight rho sigma u\<le>m"
    and db: "\<forall>u\<in>T. pair_weight rho sigma u\<le>n"
    using weyl_pair_coordinate_data[OF P Q pd qd] by blast
  have cp: "\<And>u. u\<in>S \<Longrightarrow> pair_weight rho sigma u\<le>m" using cb by blast
  have dp: "\<And>u. u\<in>T \<Longrightarrow> pair_weight rho sigma u\<le>n" using db by blast
  have pq: "pbw_symbol (op_comp P Q)=pbw_product_polynomial S T c d"
    using symbol_composition_finite_coordinates[OF fs ft, of c d] by (simp only: pc qc)
  have sp: "pbw_symbol P=coordinate_polynomial S c"
    using symbol_finite_coordinates_polynomial[OF fs, of c] by (simp only: pc)
  have sq: "pbw_symbol Q=coordinate_polynomial T d"
    using symbol_finite_coordinates_polynomial[OF ft, of d] by (simp only: qc)
  show "weighted_degree rho sigma (pbw_symbol (op_comp P Q)) \<le> bot.Value (m+n)"
    unfolding pq by (rule weighted_degree_le_of_support_bound; rule pbw_product_support_bound[OF fs ft pos cp dp])
  show "weighted_component rho sigma (m+n) (pbw_symbol (op_comp P Q)) =
      weighted_component rho sigma m (pbw_symbol P)*weighted_component rho sigma n (pbw_symbol Q)"
    unfolding pq sp sq by (rule pbw_product_top_component[OF pos cp dp])
qed
lemma symbol_mul_degree_and_leading_form:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
  shows "weighted_degree rho sigma (pbw_symbol (op_comp P Q)) = bot.Value (m+n) \<and>
    leading_form rho sigma (op_comp P Q)=leading_form rho sigma P*leading_form rho sigma Q"
proof -
  have bound: "weighted_degree rho sigma (pbw_symbol (op_comp P Q)) \<le> bot.Value (m+n)"
    by (rule symbol_mul_bound_and_top(1)[OF P Q pos pd qd])
  have top: "weighted_component rho sigma (m+n) (pbw_symbol (op_comp P Q)) =
      weighted_component rho sigma m (pbw_symbol P)*weighted_component rho sigma n (pbw_symbol Q)"
    by (rule symbol_mul_bound_and_top(2)[OF P Q pos pd qd])
  have nz: "weighted_component rho sigma (m+n) (pbw_symbol (op_comp P Q)) \<noteq> 0"
    using weighted_top_component_nonzero[OF pd] weighted_top_component_nonzero[OF qd]
    by (simp only: top mult_eq_0_iff; blast)
  have deg: "weighted_degree rho sigma (pbw_symbol (op_comp P Q))=bot.Value (m+n)"
    by (rule weighted_degree_eq_of_bound_component[OF bound nz])
  show ?thesis by (simp add: deg leading_form_def v_degree_def pd qd top)
qed
lemma symbol_commutator_degree_bound:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
  shows "weighted_degree rho sigma (pbw_symbol (op_comp P Q-op_comp Q P)) \<le> bot.Value (m+n-(rho+sigma))"
proof -
  obtain S T c d where fs: "finite S" and ft: "finite T" and pc: "finite_normal_sum S c=P"
    and qc: "finite_normal_sum T d=Q" and cb: "\<forall>u\<in>S. pair_weight rho sigma u\<le>m"
    and db: "\<forall>u\<in>T. pair_weight rho sigma u\<le>n"
    using weyl_pair_coordinate_data[OF P Q pd qd] by blast
  have cp: "\<And>u. u\<in>S \<Longrightarrow> pair_weight rho sigma u\<le>m" using cb by blast
  have dp: "\<And>u. u\<in>T \<Longrightarrow> pair_weight rho sigma u\<le>n" using db by blast
  have pq: "pbw_symbol (op_comp P Q)=pbw_product_polynomial S T c d"
    using symbol_composition_finite_coordinates[OF fs ft, of c d] by (simp only: pc qc)
  have qp: "pbw_symbol (op_comp Q P)=pbw_product_polynomial T S d c"
    using symbol_composition_finite_coordinates[OF ft fs, of d c] by (simp only: pc qc)
  have comm: "pbw_symbol (op_comp P Q-op_comp Q P)=pbw_product_polynomial S T c d-pbw_product_polynomial T S d c"
    by (simp only: weyl_symbol_sub[OF weyl_composition_closed[OF P Q] weyl_composition_closed[OF Q P]] pq qp)
  show ?thesis unfolding comm
    by (rule weighted_degree_le_of_support_bound; rule pbw_commutator_support_bound[OF fs ft pos cp dp])
qed
lemma symbol_commutator_degree_and_leading_form:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value m"
    and qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value n"
    and br: "biv_poisson (weighted_component rho sigma m (pbw_symbol P))
      (weighted_component rho sigma n (pbw_symbol Q)) \<noteq> 0"
  shows "weighted_degree rho sigma (pbw_symbol (op_comp P Q-op_comp Q P))=bot.Value (m+n-(rho+sigma)) \<and>
    leading_form rho sigma (op_comp P Q-op_comp Q P)=biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)"
proof -
  have bound: "weighted_degree rho sigma (pbw_symbol (op_comp P Q-op_comp Q P)) \<le> bot.Value (m+n-(rho+sigma))"
    by (rule symbol_commutator_degree_bound[OF P Q pos pd qd])
  have top: "weighted_component rho sigma (m+n-(rho+sigma)) (pbw_symbol (op_comp P Q-op_comp Q P)) =
      biv_poisson (weighted_component rho sigma m (pbw_symbol P)) (weighted_component rho sigma n (pbw_symbol Q))"
    by (rule symbol_commutator_top_component[OF P Q pos pd qd])
  have nz: "weighted_component rho sigma (m+n-(rho+sigma)) (pbw_symbol (op_comp P Q-op_comp Q P)) \<noteq>0"
    unfolding top by (rule br)
  have deg: "weighted_degree rho sigma (pbw_symbol (op_comp P Q-op_comp Q P))=bot.Value (m+n-(rho+sigma))"
    by (rule weighted_degree_eq_of_bound_component[OF bound nz])
  show ?thesis by (simp add: deg leading_form_def v_degree_def pd qd top)
qed
lemma weighted_degree_of_nonzero_leading_form:
  assumes "leading_form rho sigma T \<noteq> 0"
  shows "weighted_degree rho sigma (pbw_symbol T)=bot.Value (v_degree rho sigma T)"
proof -
  have nz: "pbw_symbol T\<noteq>0" using assms by (auto simp: leading_form_def)
  have nb: "weighted_degree rho sigma (pbw_symbol T)\<noteq>bot.Bot" using nz by simp
  show ?thesis using nb by (cases "weighted_degree rho sigma (pbw_symbol T)") (simp_all add: v_degree_def)
qed
lemma leading_form_commutator:
  assumes P: "P\<in>(weyl_algebra :: 'a::field_char_0 poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and pos: "0<rho+sigma"
    and br: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>0"
  shows "v_degree rho sigma (op_comp Q P-op_comp P Q)=v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma) \<and>
    leading_form rho sigma (op_comp Q P-op_comp P Q)=biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)"
proof -
  have qnz: "leading_form rho sigma Q\<noteq>0" using br by (auto simp: biv_poisson_def)
  have pnz: "leading_form rho sigma P\<noteq>0" using br by (auto simp: biv_poisson_def)
  have qd: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value (v_degree rho sigma Q)"
    by (rule weighted_degree_of_nonzero_leading_form[OF qnz])
  have pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value (v_degree rho sigma P)"
    by (rule weighted_degree_of_nonzero_leading_form[OF pnz])
  have b: "biv_poisson (weighted_component rho sigma (v_degree rho sigma Q) (pbw_symbol Q))
      (weighted_component rho sigma (v_degree rho sigma P) (pbw_symbol P))\<noteq>0"
    by (rule br[unfolded leading_form_def])
  note h = symbol_commutator_degree_and_leading_form[OF Q P pos qd pd b]
  show ?thesis using h by (simp add: v_degree_def)
qed
end
