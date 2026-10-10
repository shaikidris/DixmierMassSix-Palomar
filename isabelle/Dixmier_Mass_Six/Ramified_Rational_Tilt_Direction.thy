theory Ramified_Rational_Tilt_Direction
  imports Ramified_Grade_Exact_Pair "HOL.Rat"
begin

definition rationalTiltRho :: "nat \<Rightarrow> int \<Rightarrow> rat \<Rightarrow> int" where
  "rationalTiltRho l rho t=rho*int l*snd(quotient_of t)"
definition rationalTiltSigma :: "nat \<Rightarrow> int \<Rightarrow> rat \<Rightarrow> int" where
  "rationalTiltSigma l sigma t=sigma*int l*snd(quotient_of t)-fst(quotient_of t)"

lemma rationalTilt_weight_scale:
  "(of_int(ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) p)::rat)=
    of_nat l*of_int(snd(quotient_of t))*(of_int(ramified_weight l rho sigma p)-t*of_nat(snd p))"
proof -
  obtain a b where quotient: "quotient_of t=(a,b)" by (cases "quotient_of t") auto
  have denominator: "0<b" by (rule quotient_of_denom_pos[OF quotient])
  have fraction: "t=of_int a/of_int b" by (rule quotient_of_div[OF quotient])
  have numerator: "(t*of_int b::rat)=of_int a" using denominator by (simp add: fraction)
  show ?thesis
    by (simp only: rationalTiltRho_def rationalTiltSigma_def quotient fst_conv snd_conv
      ramified_weight_def of_int_mult of_int_diff of_int_of_nat_eq;
      simp add: algebra_simps; use numerator in blast)
qed

lemma rationalTilt_rho_pos:
  assumes l: "0<l" and rho: "0<rho"
  shows "0<rationalTiltRho l rho t"
proof -
  have denominator: "0<snd(quotient_of t)" by (rule quotient_of_denom_pos')
  show ?thesis by (simp only: rationalTiltRho_def) (intro mult_pos_pos rho denominator, use l in simp)
qed

lemma rationalTilt_sum_pos:
  assumes early: "t<(of_nat l*of_int(rho+sigma)::rat)"
  shows "0<rationalTiltRho l rho t+rationalTiltSigma l sigma t"
proof -
  obtain a b where quotient: "quotient_of t=(a,b)" by (cases "quotient_of t") auto
  have denominator: "0<b" by (rule quotient_of_denom_pos[OF quotient])
  have fraction: "t=of_int a/of_int b" by (rule quotient_of_div[OF quotient])
  have numerator: "(of_int b::rat)*t=of_int a" using denominator by (simp add: fraction)
  have multiplied: "(of_int b::rat)*t<of_int b*(of_nat l*of_int(rho+sigma))"
    by (rule mult_strict_left_mono[OF early]) (use denominator in simp)
  have rational: "(of_int a::rat)<of_int(b*int l*(rho+sigma))" using multiplied by (simp add: numerator)
  have integral: "a<b*int l*(rho+sigma)" using rational by (simp only: of_int_less_iff)
  show ?thesis using integral by (simp add: rationalTiltRho_def rationalTiltSigma_def quotient algebra_simps)
qed

lemma rationalTilt_support_bound:
  assumes l: "0<l"
    and bound: "\<And>p. p\<in>S \<Longrightarrow> (of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)\<le>
      of_int(ramified_weight l rho sigma E)-t*of_nat(snd E)"
  shows "\<forall>p\<in>S. ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) p\<le>
    ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) E"
proof (intro ballI)
  fix p assume member: "p\<in>S"
  have denominator: "0<snd(quotient_of t)" by (rule quotient_of_denom_pos')
  have scale: "(0::rat)\<le>of_nat l*of_int(snd(quotient_of t))" using l denominator by simp
  have multiplied: "of_nat l*of_int(snd(quotient_of t))*(of_int(ramified_weight l rho sigma p)-t*of_nat(snd p))\<le>
    of_nat l*of_int(snd(quotient_of t))*(of_int(ramified_weight l rho sigma E)-t*of_nat(snd E))"
    by (rule mult_left_mono[OF bound[OF member] scale])
  have rational: "(of_int(ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) p)::rat)\<le>
    of_int(ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) E)"
    using multiplied by (simp only: rationalTilt_weight_scale)
  show "ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) p\<le>
    ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) E" using rational by simp
qed

lemma rationalTilt_before_first_slope_singleton:
  fixes S :: "(int\<times>nat) set" and t tFirst :: rat
  assumes l: "0<l" and rho: "0<rho" and positive: "0<t" and before: "t<tFirst"
    and Fweight: "ramified_weight l rho sigma F=V"
    and top: "\<And>p. p\<in>S \<Longrightarrow> ramified_weight l rho sigma p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(ramified_weight l rho sigma p)-tFirst*of_nat(snd p)\<le>
      of_int V-tFirst*of_nat(snd F)"
    and member: "p\<in>S"
    and new_weight: "ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) p=
      ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) F"
  shows "p=F"
proof -
  have denominator: "0<snd(quotient_of t)" by (rule quotient_of_denom_pos')
  have scale: "(of_nat l*of_int(snd(quotient_of t))::rat)\<noteq>0" using l denominator by simp
  have multiplied: "(of_nat l*of_int(snd(quotient_of t))::rat)*(of_int(ramified_weight l rho sigma p)-t*of_nat(snd p))=
    (of_nat l*of_int(snd(quotient_of t)))*(of_int(ramified_weight l rho sigma F)-t*of_nat(snd F))"
    using arg_cong[OF new_weight, of "\<lambda>n::int. of_int n::rat"] by (simp only: rationalTilt_weight_scale)
  have tie: "(of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)=of_int V-t*of_nat(snd F)"
    using multiplied scale by (simp add: Fweight)
  show ?thesis by (rule ramifiedSupport_before_first_slope_singleton[OF rho Fweight positive before top first member tie])
qed

end
