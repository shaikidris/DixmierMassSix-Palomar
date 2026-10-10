theory Ramified_Face_Root_Multiplicity
  imports "Ramified_Face_Power_Ratio"
    "Root_Multiplicity_Adapter"
    "HOL.GCD"
begin

text \<open>Port from the pinned Palomar source. The zero-polynomial convention is
  retained by the rootMultiplicity adapter.\<close>

lemma section6_rootMultiplicity_pow:
  "rootMultiplicity a (p^n) = n * rootMultiplicity a p"
  by (simp add: rootMultiplicity_eq_count_proots proots_power)

lemma face_rootMultiplicity_smult:
  assumes "c\<noteq>0"
  shows "rootMultiplicity a ([:c:]*p) = rootMultiplicity a p"
  using assms by (cases "p=0")
    (simp_all add: rootMultiplicity_eq_order order_smult)

lemma rootMultiplicity_dvd_of_coprime_power_ratio:
  fixes f g :: "complex poly" and A D n d :: nat
  assumes "0<A" "D*d=A*n" "coprime d n"
    "\<forall>a. D * rootMultiplicity a f = A * rootMultiplicity a g"
  shows "d dvd rootMultiplicity a f"
proof -
  have equation: "A * (n * rootMultiplicity a f) =
      A * (d * rootMultiplicity a g)"
  proof -
    have "A * (n * rootMultiplicity a f) = (D*d)*rootMultiplicity a f"
      by (simp only: assms(2) mult.assoc)
    also have "... = d * (D * rootMultiplicity a f)"
      by (simp add: mult_ac)
    also have "... = d * (A * rootMultiplicity a g)"
      using assms(4) by simp
    also have "... = A * (d * rootMultiplicity a g)"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have cancelled: "n * rootMultiplicity a f = d * rootMultiplicity a g"
    using equation assms(1) by simp
  have "d dvd rootMultiplicity a f * n"
    using cancelled by (simp add: mult.commute)
  then show ?thesis using assms(3)
    by (simp add: coprime_dvd_mult_left_iff)
qed

lemma ramified_exact_pair_top_face_rootMultiplicity_ratio:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  shows "nat (ramified_weight_deg l rho sigma Q) *
      rootMultiplicity a (ramified_top_face_polynomial l rho sigma P) =
    nat (ramified_weight_deg l rho sigma P) *
      rootMultiplicity a (ramified_top_face_polynomial l rho sigma Q)"
proof -
  obtain c where cnz: "c\<noteq>0" and ratio:
    "ramified_top_face_polynomial l rho sigma P ^ nat (ramified_weight_deg l rho sigma Q)=
      [:c:] * ramified_top_face_polynomial l rho sigma Q ^ nat (ramified_weight_deg l rho sigma P)"
    using ramified_exact_pair_top_face_power_ratio[OF assms] by blast
  note roots = arg_cong[OF ratio, of "rootMultiplicity a"]
  show ?thesis using roots
    by (simp only: section6_rootMultiplicity_pow face_rootMultiplicity_smult[OF cnz])
qed

lemma ramified_exact_pair_top_face_rootMultiplicity_dvd:
  fixes n d :: nat
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    "nat (ramified_weight_deg l rho sigma Q)*d = nat (ramified_weight_deg l rho sigma P)*n"
    "coprime d n"
  shows "d dvd rootMultiplicity a (ramified_top_face_polynomial l rho sigma P)"
proof -
  have positive: "0<nat (ramified_weight_deg l rho sigma P)" using assms(9) by simp
  have roots: "\<forall>z. nat (ramified_weight_deg l rho sigma Q) *
      rootMultiplicity z (ramified_top_face_polynomial l rho sigma P) =
    nat (ramified_weight_deg l rho sigma P) *
      rootMultiplicity z (ramified_top_face_polynomial l rho sigma Q)"
    using ramified_exact_pair_top_face_rootMultiplicity_ratio[OF assms(1-11)] by blast
  show ?thesis
    by (rule rootMultiplicity_dvd_of_coprime_power_ratio[OF positive assms(12,13) roots])
qed

end
