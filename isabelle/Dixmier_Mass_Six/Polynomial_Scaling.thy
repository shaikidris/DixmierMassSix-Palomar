theory Polynomial_Scaling
  imports "Sparse_Support"
begin

text \<open>Source: DixmierFormal/Scalar/Scaling.lean at the pinned source commit.
All eight public statements retain the source's field sort and premises.\<close>

lemma coeff_comp_C_mul_X:
  fixes p :: "'a::field poly"
  shows "coeff (pcompose p [:0,c:]) n = coeff p n * c ^ n"
  by (simp add: coeff_pcompose_linear mult.commute)

lemma support_comp_C_mul_X:
  fixes p :: "'a::field poly"
  assumes hc: "c \<noteq> 0"
  shows "sparse_support (pcompose p [:0,c:]) = sparse_support p"
  using hc by (auto simp: sparse_support_def coeff_comp_C_mul_X)

lemma termCount_comp_C_mul_X:
  fixes p :: "'a::field poly"
  assumes hc: "c \<noteq> 0"
  shows "termCount (pcompose p [:0,c:]) = termCount p"
  by (simp only: termCount_def support_comp_C_mul_X[OF hc])

lemma comp_C_mul_X_comp_C_inv_mul_X:
  fixes p :: "'a::field poly"
  assumes hc: "c \<noteq> 0"
  shows "pcompose (pcompose p [:0,c:]) [:0,inverse c:] = p"
proof -
  have linear: "pcompose [:0,c:] [:0,inverse c:] = [:0,1:]"
    using hc by (simp add: pcompose_pCons)
  show ?thesis by (simp only: pcompose_assoc[symmetric] linear pcompose_idR)
qed

lemma X_sub_C_comp_C_mul_X:
  fixes a c :: "'a::field"
  assumes hc: "c \<noteq> 0"
  shows "pcompose [:-a,1:] [:0,c:] = [:c:] * [:- (a / c),1:]"
  using hc by (simp add: pcompose_pCons field_simps)

lemma pow_dvd_comp_C_mul_X:
  fixes S :: "'a::field poly"
  assumes hc: "c \<noteq> 0"
    and h: "[:-a,1:] ^ m dvd S"
  shows "[:- (a / c),1:] ^ m dvd pcompose S [:0,c:]"
proof -
  obtain q where S: "S = [:-a,1:] ^ m * q"
    using h by (auto simp: dvd_def)
  have power_comp: "pcompose (p ^ k) [:0,c:] = (pcompose p [:0,c:]) ^ k"
    for p :: "'a poly" and k
    by (induction k) (simp_all add: pcompose_mult pcompose_1)
  have "pcompose S [:0,c:] =
      ([:c:] * [:- (a / c),1:]) ^ m * pcompose q [:0,c:]"
    by (simp only: S pcompose_mult power_comp X_sub_C_comp_C_mul_X[OF hc])
  also have "\<dots> = [:- (a / c),1:] ^ m * ([:c:] ^ m * pcompose q [:0,c:])"
    by (simp only: power_mult_distrib mult_ac)
  finally show ?thesis by (auto simp: dvd_def)
qed

lemma natDegree_comp_C_mul_X:
  fixes p :: "'a::field poly"
  assumes hc: "c \<noteq> 0"
  shows "degree (pcompose p [:0,c:]) = degree p"
  using hc by (simp add: degree_pcompose)

lemma eval_zero_comp_C_mul_X:
  fixes p :: "'a::field poly"
  shows "poly (pcompose p [:0,c:]) 0 = poly p 0"
  by (simp add: poly_pcompose)

end
