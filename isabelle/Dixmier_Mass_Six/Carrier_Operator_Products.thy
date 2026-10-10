theory Carrier_Operator_Products
  imports "Carrier_Weyl_Span_Descent"
begin

context dixmier_carrier_char_zero_embedding
begin

lemma carrier_base_change_zero [simp]: "concrete_base_change f 0 = 0"
  using carrier_base_change_finite_normal_sum[OF finite.emptyI, of "\<lambda>_. 0"] by simp
lemma carrier_base_change_normal_monomial:
  "concrete_base_change f (normal_monomial a b) = normal_monomial a b"
  using carrier_base_change_finite_normal_sum[of "{(a,b)}" "\<lambda>_. 1"]
  by (simp add: finite_normal_sum_def map_one)
lemma carrier_base_change_id [simp]: "concrete_base_change f id = id"
  using carrier_base_change_normal_monomial[of 0 0] by simp
lemma carrier_base_change_x [simp]: "concrete_base_change f x_op = x_op"
  using carrier_base_change_normal_monomial[of 1 0] by (simp add: normal_monomial_def)
lemma carrier_base_change_y [simp]: "concrete_base_change f y_op = y_op"
  using carrier_base_change_normal_monomial[of 0 1] by (simp add: normal_monomial_def)
lemma carrier_weyl_id: "id \<in> carrier_weyl E"
  using carrier_weyl_normal_monomial[of 0 0] by simp
lemma carrier_weyl_x: "x_op \<in> carrier_weyl E"
  using carrier_weyl_normal_monomial[of 1 0] by (simp add: normal_monomial_def)
lemma carrier_weyl_y: "y_op \<in> carrier_weyl E"
  using carrier_weyl_normal_monomial[of 0 1] by (simp add: normal_monomial_def)

lemma carrier_base_change_sum:
  assumes "finite J" "\<And>j. j \<in> J \<Longrightarrow> T j \<in> carrier_weyl E"
  shows "concrete_base_change f (\<Sum>j\<in>J. T j) = (\<Sum>j\<in>J. concrete_base_change f (T j))"
  using assms
proof (induction J rule: finite_induct)
  case empty then show ?case by (simp only: sum.empty carrier_base_change_zero)
next
  case (insert j J)
  have tj: "T j \<in> carrier_weyl E" by (rule insert.prems) simp
  have tail: "\<And>k. k \<in> J \<Longrightarrow> T k \<in> carrier_weyl E" by (rule insert.prems) simp
  have ts: "(\<Sum>k\<in>J. T k) \<in> carrier_weyl E" by (rule carrier_weyl_sum[OF insert.hyps(1) tail])
  show ?case by (simp only: sum.insert[OF insert.hyps] carrier_base_change_add[OF tj ts] insert.IH[OF tail])
qed

lemma carrier_base_change_diff:
  assumes T: "T \<in> carrier_weyl E" and U: "U \<in> carrier_weyl E"
  shows "concrete_base_change f (T-U) = concrete_base_change f T - concrete_base_change f U"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change f (T-U) \<in> weyl_algebra"
    by (intro carrier_base_change_in_weyl bc_weyl_diff carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U])
  show "concrete_base_change f T - concrete_base_change f U \<in> weyl_algebra"
    by (intro bc_weyl_diff carrier_base_change_in_weyl carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U])
  fix a b
  show "pbw_coeff (concrete_base_change f (T-U)) a b =
      pbw_coeff (concrete_base_change f T - concrete_base_change f U) a b"
    by (simp only: carrier_base_change_coeff[OF bc_weyl_diff[OF carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U]]]
        bc_pbw_coeff_diff carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF T]]
        carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF U]]
        map_diff_on[OF carrier_weyl_coeff[OF T] carrier_weyl_coeff[OF U]])
qed

lemma carrier_normal_terms:
  assumes fin: "finite J" and ce: "\<And>j. j \<in> J \<Longrightarrow> c j \<in> E"
  shows "(\<Sum>j\<in>J. (\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p))) \<in> carrier_weyl E"
  by (intro carrier_weyl_sum[OF fin] carrier_weyl_smult carrier_weyl_normal_monomial ce)
lemma carrier_base_change_normal_terms:
  assumes fin: "finite J" and ce: "\<And>j. j \<in> J \<Longrightarrow> c j \<in> E"
  shows "concrete_base_change f (\<Sum>j\<in>J. (\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p))) =
    (\<Sum>j\<in>J. (\<lambda>p. smult (f (c j)) (normal_monomial (a j) (b j) p)))"
proof -
  have terms: "(\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p)) \<in> carrier_weyl E"
    if "j \<in> J" for j by (intro carrier_weyl_smult carrier_weyl_normal_monomial ce[OF that])
  have mapped: "concrete_base_change f (\<Sum>j\<in>J. (\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p))) =
    (\<Sum>j\<in>J. concrete_base_change f (\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p)))"
    by (rule carrier_base_change_sum[OF fin terms])
  show ?thesis unfolding mapped
  proof (rule sum.cong[OF refl])
    fix j assume ji: "j \<in> J"
    show "concrete_base_change f (\<lambda>p. smult (c j) (normal_monomial (a j) (b j) p)) =
      (\<lambda>p. smult (f (c j)) (normal_monomial (a j) (b j) p))"
      by (simp only: carrier_base_change_smult[OF carrier_weyl_normal_monomial ce[OF ji]] carrier_base_change_normal_monomial)
  qed
qed

lemma carrier_finite_normal_product:
  assumes sf: "finite S" and tf: "finite T"
    and ce: "\<And>u. u \<in> S \<Longrightarrow> c u \<in> E"
    and de: "\<And>v. v \<in> T \<Longrightarrow> d v \<in> E"
  shows "op_comp (finite_normal_sum S c) (finite_normal_sum T d) \<in> carrier_weyl E"
  unfolding finite_normal_sum_mul[OF sf tf]
  by (intro carrier_weyl_sum[OF sf] carrier_weyl_sum[OF tf] carrier_normal_terms finite_atMost
      E_mult E_of_nat ce de)

lemma carrier_base_change_finite_product:
  assumes sf: "finite S" and tf: "finite T"
    and ce: "\<And>u. u \<in> S \<Longrightarrow> c u \<in> E"
    and de: "\<And>v. v \<in> T \<Longrightarrow> d v \<in> E"
  shows "concrete_base_change f (op_comp (finite_normal_sum S c) (finite_normal_sum T d)) =
    op_comp (finite_normal_sum S (f \<circ> c)) (finite_normal_sum T (f \<circ> d))"
proof -
  let ?C = "\<lambda>u v k. c u*d v*of_nat ((snd u choose k)*nat_desc_factorial (fst v) k)"
  let ?N = "\<lambda>u v k. normal_monomial (fst u+fst v-k) (snd u+snd v-k)"
  let ?J = "\<lambda>u v. {..min (fst v) (snd u)}"
  have coeff: "?C u v k \<in> E" if "u \<in> S" "v \<in> T" for u v k
    by (intro E_mult ce[OF that(1)] de[OF that(2)] E_of_nat)
  have inner: "(\<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) \<in> carrier_weyl E"
    if "u \<in> S" "v \<in> T" for u v
    by (intro carrier_normal_terms finite_atMost coeff[OF that])
  have middle: "(\<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) \<in> carrier_weyl E"
    if "u \<in> S" for u
    by (intro carrier_weyl_sum[OF tf] inner[OF that])
  have outer_map: "concrete_base_change f
      (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) =
      (\<Sum>u\<in>S. concrete_base_change f (\<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))))"
    by (rule carrier_base_change_sum[OF sf middle])
  have mapping: "concrete_base_change f
      (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) =
      (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (f (?C u v k)) (?N u v k p)))"
  proof (rule trans[OF outer_map], rule sum.cong[OF refl])
    fix u assume us: "u \<in> S"
    have inner_map: "concrete_base_change f
        (\<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) =
        (\<Sum>v\<in>T. concrete_base_change f (\<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))))"
      by (rule carrier_base_change_sum[OF tf inner[OF us]])
    show "concrete_base_change f
        (\<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) =
        (\<Sum>v\<in>T. \<Sum>k\<in>?J u v. (\<lambda>p. smult (f (?C u v k)) (?N u v k p)))"
    proof (rule trans[OF inner_map], rule sum.cong[OF refl])
      fix v assume vt: "v \<in> T"
      show "concrete_base_change f (\<Sum>k\<in>?J u v. (\<lambda>p. smult (?C u v k) (?N u v k p))) =
        (\<Sum>k\<in>?J u v. (\<lambda>p. smult (f (?C u v k)) (?N u v k p)))"
        by (rule carrier_base_change_normal_terms[OF finite_atMost]) (rule coeff[OF us vt])
    qed
  qed
  have mapped_coeff: "f (?C u v k) = f (c u)*f (d v)*of_nat ((snd u choose k)*nat_desc_factorial (fst v) k)"
    if "u \<in> S" "v \<in> T" for u v k
    by (simp only: map_mult_on[OF E_mult[OF ce[OF that(1)] de[OF that(2)]] E_of_nat]
        map_mult_on[OF ce[OF that(1)] de[OF that(2)]] map_of_nat)
  show ?thesis
    unfolding finite_normal_sum_mul[OF sf tf] mapping comp_apply
    by (intro sum.cong refl) (simp only: mapped_coeff)
qed

lemma carrier_weyl_finite_coordinates:
  assumes T: "T \<in> carrier_weyl E"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> (\<forall>u. c u \<in> E) \<and>
    finite_normal_sum {u. c u \<noteq> 0} c = T"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and ct: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF carrier_weyl_in_weyl[OF T]] by blast
  have ce: "c u \<in> E" for u
  proof -
    have "c u = pbw_coeff T (fst u) (snd u)"
      using pbw_coeff_finite_coordinates[OF cf, of "fst u" "snd u"] ct by simp
    then show ?thesis using carrier_weyl_coeff[OF T, of "fst u" "snd u"] by simp
  qed
  show ?thesis by (rule exI[of _ c]) (simp only: cf ct ce simp_thms)
qed

lemma carrier_weyl_comp:
  assumes T: "T \<in> carrier_weyl E" and U: "U \<in> carrier_weyl E"
  shows "op_comp T U \<in> carrier_weyl E"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and ce: "\<forall>u. c u \<in> E"
    and ct: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using carrier_weyl_finite_coordinates[OF T] by blast
  obtain d where df: "finite {u. d u \<noteq> 0}" and de: "\<forall>u. d u \<in> E"
    and du: "finite_normal_sum {u. d u \<noteq> 0} d = U"
    using carrier_weyl_finite_coordinates[OF U] by blast
  have "op_comp (finite_normal_sum {u. c u \<noteq> 0} c) (finite_normal_sum {u. d u \<noteq> 0} d) \<in> carrier_weyl E"
    by (rule carrier_finite_normal_product[OF cf df]) (intro ce[rule_format] de[rule_format])+
  then show ?thesis by (simp only: ct du)
qed
lemma carrier_base_change_comp:
  assumes T: "T \<in> carrier_weyl E" and U: "U \<in> carrier_weyl E"
  shows "concrete_base_change f (op_comp T U) = op_comp (concrete_base_change f T) (concrete_base_change f U)"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and ce: "\<forall>u. c u \<in> E"
    and ct: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using carrier_weyl_finite_coordinates[OF T] by blast
  obtain d where df: "finite {u. d u \<noteq> 0}" and de: "\<forall>u. d u \<in> E"
    and du: "finite_normal_sum {u. d u \<noteq> 0} d = U"
    using carrier_weyl_finite_coordinates[OF U] by blast
  have cm: "concrete_base_change f T = finite_normal_sum {u. c u \<noteq> 0} (f \<circ> c)"
    using carrier_base_change_finite_normal_sum[OF cf, of c] ct by simp
  have dm: "concrete_base_change f U = finite_normal_sum {u. d u \<noteq> 0} (f \<circ> d)"
    using carrier_base_change_finite_normal_sum[OF df, of d] du by simp
  have "concrete_base_change f (op_comp (finite_normal_sum {u. c u \<noteq> 0} c)
      (finite_normal_sum {u. d u \<noteq> 0} d)) =
    op_comp (finite_normal_sum {u. c u \<noteq> 0} (f \<circ> c)) (finite_normal_sum {u. d u \<noteq> 0} (f \<circ> d))"
    by (rule carrier_base_change_finite_product[OF cf df]) (intro ce[rule_format] de[rule_format])+
  then show ?thesis by (simp only: ct du cm dm)
qed
lemma carrier_base_change_commutator_one:
  assumes P: "P \<in> carrier_weyl E" and Q: "Q \<in> carrier_weyl E"
    and eq: "op_comp Q P - op_comp P Q = id"
  shows "op_comp (concrete_base_change f Q) (concrete_base_change f P) -
    op_comp (concrete_base_change f P) (concrete_base_change f Q) = id"
  using arg_cong[OF eq, of "concrete_base_change f"]
  by (simp only: carrier_base_change_diff[OF carrier_weyl_comp[OF Q P] carrier_weyl_comp[OF P Q]]
      carrier_base_change_comp[OF Q P] carrier_base_change_comp[OF P Q] carrier_base_change_id)

end
end
