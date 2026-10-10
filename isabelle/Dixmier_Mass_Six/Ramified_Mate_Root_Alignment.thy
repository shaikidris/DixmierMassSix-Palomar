theory Ramified_Mate_Root_Alignment
  imports "Ramified_Face_Root_Multiplicity"
begin

lemma ramified_exact_pair_top_face_degree_ratio:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  shows "nat (ramified_weight_deg l rho sigma Q) *
      degree (ramified_top_face_polynomial l rho sigma P) =
    nat (ramified_weight_deg l rho sigma P) *
      degree (ramified_top_face_polynomial l rho sigma Q)"
proof -
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma Q"
  obtain c where cnz: "c\<noteq>0" and ratio:
    "?f ^ nat (ramified_weight_deg l rho sigma Q)=
      [:c:] * ?g ^ nat (ramified_weight_deg l rho sigma P)"
    using ramified_exact_pair_top_face_power_ratio[OF assms] by blast
  have fnz: "?f\<noteq>0"
    by (rule ramified_top_face_polynomial_ne_zero[OF assms(1,4,2,6)])
  have gnz: "?g\<noteq>0"
    by (rule ramified_top_face_polynomial_ne_zero[OF assms(1,5,2,7)])
  note degrees = arg_cong[OF ratio, of degree]
  show ?thesis using degrees cnz fnz gnz by (simp add: degree_power_eq)
qed

lemma ramified_exact_pair_full_degree_root_mate:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=
      degree (ramified_top_face_polynomial l rho sigma P)"
  shows "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=
      degree (ramified_top_face_polynomial l rho sigma Q)"
proof -
  note roots = ramified_exact_pair_top_face_rootMultiplicity_ratio[OF assms(1-11), where a=c]
  note degrees = ramified_exact_pair_top_face_degree_ratio[OF assms(1-11)]
  have equal:
    "nat (ramified_weight_deg l rho sigma P) *
      rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=
    nat (ramified_weight_deg l rho sigma P) *
      degree (ramified_top_face_polynomial l rho sigma Q)"
    using roots degrees assms(12) by metis
  have positive: "0<nat (ramified_weight_deg l rho sigma P)" using assms(9) by simp
  show ?thesis using equal positive by simp
qed

lemma ramified_exact_pair_full_degree_root_mate_of_reverse_commutator:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp Q P-laurent_comp P Q=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=
      degree (ramified_top_face_polynomial l rho sigma P)"
  shows "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=
      degree (ramified_top_face_polynomial l rho sigma Q)"
proof -
  have threshold: "0<ramified_weight_deg l rho sigma Q+
      ramified_weight_deg l rho sigma P-int l*(rho+sigma)"
    using assms(11) by (simp add: add.commute)
  note roots = ramified_exact_pair_top_face_rootMultiplicity_ratio[
    OF assms(1,2,3,5,4,7,6,8,10,9) threshold, where a=c]
  note degrees = ramified_exact_pair_top_face_degree_ratio[
    OF assms(1,2,3,5,4,7,6,8,10,9) threshold]
  have equal:
    "nat (ramified_weight_deg l rho sigma P) *
      rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=
    nat (ramified_weight_deg l rho sigma P) *
      degree (ramified_top_face_polynomial l rho sigma Q)"
    using roots degrees assms(12) by metis
  have positive: "0<nat (ramified_weight_deg l rho sigma P)" using assms(9) by simp
  show ?thesis using equal positive by simp
qed

end
