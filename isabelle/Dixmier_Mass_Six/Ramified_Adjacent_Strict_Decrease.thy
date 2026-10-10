theory Ramified_Adjacent_Strict_Decrease
  imports Ramified_Corner_Endpoint_Geometry
begin

lemma ramified_lower_order_tie_direction_strict_decrease:
  fixes l :: nat and rho sigma r s :: int and E B :: "int\<times>nat"
  assumes l: "0<l" and r: "0<r" and order: "snd B<snd E"
    and old: "ramified_weight l rho sigma B<ramified_weight l rho sigma E"
    and tie: "ramified_weight l r s B=ramified_weight l r s E"
  shows "rho*s<r*sigma"
proof -
  have algebra: "r*(ramified_weight l rho sigma E-ramified_weight l rho sigma B)-
    int l*(int(snd E)-int(snd B))*(r*sigma-rho*s)=
    rho*(ramified_weight l r s E-ramified_weight l r s B)"
    by (simp add: ramified_weight_def algebra_simps)
  have identity: "r*(ramified_weight l rho sigma E-ramified_weight l rho sigma B)=
    int l*(int(snd E)-int(snd B))*(r*sigma-rho*s)"
    using algebra tie by simp
  have delta: "0<int(snd E)-int(snd B)" using order by simp
  have factor: "0<int l*(int(snd E)-int(snd B))"
    by (rule mult_pos_pos) (use l delta in auto)
  have product: "0<r*(ramified_weight l rho sigma E-ramified_weight l rho sigma B)"
    by (rule mult_pos_pos) (use r old in auto)
  have positive: "0<int l*(int(snd E)-int(snd B))*(r*sigma-rho*s)"
    using identity product by simp
  have "0<r*sigma-rho*s"
    using positive factor by (auto simp only: zero_less_mult_iff; arith)
  then show ?thesis by arith
qed

lemma ramified_old_face_min_order_new_tie_strict_decrease:
  fixes l :: nat and rho sigma r s :: int and P :: laurent_operator and E B :: "int\<times>nat"
  assumes l: "0<l" and r: "0<r" and carrier: "P\<in>ramified_operator_algebra l"
    and B: "B\<in>ramified_pbw_support l P"
    and top: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
    and minimum: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
      ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P \<Longrightarrow> snd E\<le>snd p"
    and order: "snd B<snd E"
    and tie: "ramified_weight l r s B=ramified_weight l r s E"
  shows "rho*s<r*sigma"
proof -
  have upper: "ramified_weight l rho sigma B\<le>ramified_weight_deg l rho sigma P"
    by (rule ramified_weight_deg_upper[OF B])
  have unequal: "ramified_weight l rho sigma B\<noteq>ramified_weight_deg l rho sigma P"
  proof
    assume equal: "ramified_weight l rho sigma B=ramified_weight_deg l rho sigma P"
    have "snd E\<le>snd B" by (rule minimum[OF B equal])
    then show False using order by arith
  qed
  have strict: "ramified_weight l rho sigma B<ramified_weight l rho sigma E"
    using upper unequal top by arith
  show ?thesis by (rule ramified_lower_order_tie_direction_strict_decrease[OF l r order strict tie])
qed

end
