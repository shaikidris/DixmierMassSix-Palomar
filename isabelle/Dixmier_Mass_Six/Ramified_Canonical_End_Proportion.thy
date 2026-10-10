theory Ramified_Canonical_End_Proportion
  imports Ramified_Corner_Endpoint_Geometry
    "Ramified_Mate_Root_Alignment"
begin

lemma ramified_exact_pair_canonical_ends_proportional:
  fixes l n d :: nat and rho sigma :: int and P Q :: laurent_operator
  assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
    and comm: "laurent_comp Q P-laurent_comp P Q=id"
    and A: "0<ramified_weight_deg l rho sigma P"
    and D: "0<ramified_weight_deg l rho sigma Q"
    and threshold: "0<ramified_weight_deg l rho sigma P+
      ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    and ratio: "ramified_weight_deg l rho sigma Q*int d=
      ramified_weight_deg l rho sigma P*int n"
  shows "int n*ramified_pbw_top_laurent l P
      (degree (ramified_top_face_polynomial l rho sigma P))=
    int d*ramified_pbw_top_laurent l Q
      (degree (ramified_top_face_polynomial l rho sigma Q)) \<and>
    n*degree (ramified_top_face_polynomial l rho sigma P)=
      d*degree (ramified_top_face_polynomial l rho sigma Q)"
proof -
  let ?a = "ramified_weight_deg l rho sigma P"
  let ?b = "ramified_weight_deg l rho sigma Q"
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma Q"
  let ?u = "degree ?f" let ?v = "degree ?g"
  let ?x = "ramified_pbw_top_laurent l P ?u"
  let ?y = "ramified_pbw_top_laurent l Q ?v"
  have reversed_threshold: "0<?b+?a-int l*(rho+sigma)"
    using threshold by (simp add: add.commute)
  have degree_ratio: "nat ?a*?v=nat ?b*?u"
    by (rule ramified_exact_pair_top_face_degree_ratio[where l=l and rho=rho and sigma=sigma and P=Q and Q=P, OF l rho sum Q P Qnz Pnz comm D A reversed_threshold])
  have degree_ratio_int: "?a*int ?v=?b*int ?u"
    using arg_cong[OF degree_ratio, of int] A D by simp
  have scaled: "?a*(int n*int ?u)=?a*(int d*int ?v)"
  proof -
    have "?a*(int n*int ?u)=(?a*int n)*int ?u" by (simp add: algebra_simps)
    also have "\<dots>=(?b*int d)*int ?u" using ratio by simp
    also have "\<dots>=int d*(?b*int ?u)" by (simp add: algebra_simps)
    also have "\<dots>=int d*(?a*int ?v)" using degree_ratio_int by simp
    also have "\<dots>=?a*(int d*int ?v)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hy_int: "int n*int ?u=int d*int ?v"
    using scaled A by simp
  have hy: "n*?u=d*?v"
    using hy_int by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
  have fnz: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
  have gnz: "?g\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l Q rho Qnz])
  have fp: "?u\<in>polynomial_support ?f"
    using fnz by (simp add: polynomial_support_def)
  have gp: "?v\<in>polynomial_support ?g"
    using gnz by (simp add: polynomial_support_def)
  have endpointP: "rho*?x+int l*sigma*int ?u=?a"
    using fp by (simp only: ramified_top_face_polynomial_mem_support_iff)
  have endpointQ: "rho*?y+int l*sigma*int ?v=?b"
    using gp by (simp only: ramified_top_face_polynomial_mem_support_iff)
  have endpointP_scaled: "(rho*?x+int l*sigma*int ?u)*int n=?a*int n"
    using endpointP by simp
  have endpointQ_scaled: "(rho*?y+int l*sigma*int ?v)*int d=?b*int d"
    using endpointQ by simp
  have orders_scaled: "int l*sigma*(int n*int ?u)=int l*sigma*(int d*int ?v)"
    using hy_int by simp
  have difference: "rho*(int n*?x-int d*?y)=0"
  proof -
    have "rho*(int n*?x-int d*?y)=
      (rho*?x+int l*sigma*int ?u)*int n-
      (rho*?y+int l*sigma*int ?v)*int d-
      int l*sigma*(int n*int ?u-int d*int ?v)"
      by (simp add: algebra_simps)
    also have "\<dots>=?a*int n-?b*int d"
      by (simp only: endpointP endpointQ hy_int diff_self mult_zero_right diff_0_right)
    also have "\<dots>=0" using ratio by simp
    finally show ?thesis .
  qed
  have difference_zero: "int n*?x-int d*?y=0" using difference rho by simp
  have hx: "int n*?x=int d*?y" using difference_zero by arith
  show ?thesis using hx hy by blast
qed

end
