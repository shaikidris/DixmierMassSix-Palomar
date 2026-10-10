theory Ramified_Common_Integral_Face
  imports Ramified_Rational_Tilt_Direction
begin

lemma rationalTilt_tied_weight:
  assumes l: "0<l"
    and tie: "(of_int(ramified_weight l rho sigma B)::rat)-t*of_nat(snd B)=
      of_int(ramified_weight l rho sigma E)-t*of_nat(snd E)"
  shows "ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) B=
    ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) E"
proof -
  have multiplied: "(of_nat l*of_int(snd(quotient_of t))::rat)*(of_int(ramified_weight l rho sigma B)-t*of_nat(snd B))=
    (of_nat l*of_int(snd(quotient_of t)))*(of_int(ramified_weight l rho sigma E)-t*of_nat(snd E))"
    by (rule arg_cong[OF tie])
  have rational: "(of_int(ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) B)::rat)=
    of_int(ramified_weight l (rationalTiltRho l rho t) (rationalTiltSigma l sigma t) E)"
    using multiplied by (simp only: rationalTilt_weight_scale)
  show ?thesis using rational by simp
qed

lemma ramified_common_rational_tilt_integral_face:
  assumes l: "0<l" and rho: "0<rho"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and early: "t<(of_nat l*of_int(rho+sigma)::rat)"
    and E: "E\<in>ramified_pbw_support l P" and F: "F\<in>ramified_pbw_support l Q"
    and BP: "BP\<in>ramified_pbw_support l P" and BQ: "BQ\<in>ramified_pbw_support l Q"
    and Eweight: "ramified_weight l rho sigma E=VP" and Fweight: "ramified_weight l rho sigma F=VQ"
    and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
      (of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd E)"
    and Qfirst: "\<And>p. p\<in>ramified_pbw_support l Q \<Longrightarrow>
      (of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)\<le>of_int VQ-t*of_nat(snd F)"
    and BPtie: "(of_int(ramified_weight l rho sigma BP)::rat)-t*of_nat(snd BP)=of_int VP-t*of_nat(snd E)"
    and BQtie: "(of_int(ramified_weight l rho sigma BQ)::rat)-t*of_nat(snd BQ)=of_int VQ-t*of_nat(snd F)"
  shows "\<exists>rho' sigma'::int. rho'=rationalTiltRho l rho t \<and> sigma'=rationalTiltSigma l sigma t \<and>
    0<rho' \<and> 0<rho'+sigma' \<and>
    (\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho' sigma' p\<le>ramified_weight l rho' sigma' E) \<and>
    (\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l rho' sigma' q\<le>ramified_weight l rho' sigma' F) \<and>
    ramified_weight l rho' sigma' E=ramified_weight_deg l rho' sigma' P \<and>
    ramified_weight l rho' sigma' F=ramified_weight_deg l rho' sigma' Q \<and>
    ramified_weight l rho' sigma' BP=ramified_weight_deg l rho' sigma' P \<and>
    ramified_weight l rho' sigma' BQ=ramified_weight_deg l rho' sigma' Q"
proof -
  let ?r = "rationalTiltRho l rho t"
  let ?s = "rationalTiltSigma l sigma t"
  have r: "0<?r" by (rule rationalTilt_rho_pos[OF l rho])
  have sum: "0<?r+?s" by (rule rationalTilt_sum_pos[OF early])
  have Pbound: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l ?r ?s p\<le>ramified_weight l ?r ?s E"
    by (rule rationalTilt_support_bound[OF l]) (use Pfirst in \<open>simp only: Eweight\<close>)
  have Qbound: "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l ?r ?s q\<le>ramified_weight l ?r ?s F"
    by (rule rationalTilt_support_bound[OF l]) (use Qfirst in \<open>simp only: Fweight\<close>)
  have Etop: "ramified_weight l ?r ?s E=ramified_weight_deg l ?r ?s P"
    by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use E Pbound in auto)
  have Ftop: "ramified_weight l ?r ?s F=ramified_weight_deg l ?r ?s Q"
    by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use F Qbound in auto)
  have BPE: "ramified_weight l ?r ?s BP=ramified_weight l ?r ?s E"
    by (rule rationalTilt_tied_weight[OF l]) (use BPtie in \<open>simp only: Eweight\<close>)
  have BQF: "ramified_weight l ?r ?s BQ=ramified_weight l ?r ?s F"
    by (rule rationalTilt_tied_weight[OF l]) (use BQtie in \<open>simp only: Fweight\<close>)
  have BPtop: "ramified_weight l ?r ?s BP=ramified_weight_deg l ?r ?s P"
    by (rule trans[OF BPE Etop])
  have BQtop: "ramified_weight l ?r ?s BQ=ramified_weight_deg l ?r ?s Q"
    by (rule trans[OF BQF Ftop])
  show ?thesis
    by (rule exI[where x="?r"], rule exI[where x="?s"], intro conjI)
       (rule refl r sum Pbound Qbound Etop Ftop BPtop BQtop)+
qed

lemma ramified_common_integral_face_primitive:
  assumes l: "0<l" and R: "0<R" and sum: "0<R+S"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and E: "E\<in>ramified_pbw_support l P" and F: "F\<in>ramified_pbw_support l Q"
    and Pupper: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l R S p\<le>ramified_weight l R S E"
    and Qupper: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l R S q\<le>ramified_weight l R S F"
    and Ptie: "ramified_weight l R S BP=ramified_weight l R S E"
    and Qtie: "ramified_weight l R S BQ=ramified_weight l R S F"
  shows "\<exists>r s g::int. 0<g \<and> R=g*r \<and> S=g*s \<and> is_direction r s \<and> 0<r \<and>
    ramified_weight l r s E=ramified_weight_deg l r s P \<and>
    ramified_weight l r s F=ramified_weight_deg l r s Q \<and>
    ramified_weight l r s BP=ramified_weight_deg l r s P \<and>
    ramified_weight l r s BQ=ramified_weight_deg l r s Q"
proof -
  let ?g = "gcd R S"
  let ?r = "R div ?g"
  let ?s = "S div ?g"
  have g: "0<?g" using R by simp
  have Re: "R=?g*?r" by (simp add: dvd_mult_div_cancel gcd_dvd1)
  have Se: "S=?g*?s" by (simp add: dvd_mult_div_cancel gcd_dvd2)
  have product_positive: "0<?g*?r" using R Re by arith
  have r: "0<?r" using product_positive g by (simp only: zero_less_mult_iff; arith)
  have summed: "?g*(?r+?s)=R+S" by (simp only: distrib_left Re[symmetric] Se[symmetric])
  have product_sum_positive: "0<?g*(?r+?s)" using sum summed by arith
  have positive: "0<?r+?s" using product_sum_positive g
    by (simp only: zero_less_mult_iff; arith)
  have coprime: "coprime ?r ?s" by (rule div_gcd_coprime) (use R in auto)
  have gcd_integer: "gcd ?r ?s=1"
    using coprime by (simp only: coprime_iff_gcd_eq_1)
  have gcd_cast: "int(gcd(nat(abs ?r))(nat(abs ?s)))=int 1"
    using gcd_integer by (simp only: gcd_int_def of_nat_1)
  have gcd_nat: "gcd(nat(abs ?r))(nat(abs ?s))=1"
    using gcd_cast by (simp only: of_nat_eq_iff)
  have direction: "is_direction ?r ?s"
    unfolding is_direction_def using gcd_nat positive by blast
  have scale: "\<And>p. ramified_weight l R S p=?g*ramified_weight l ?r ?s p"
  proof -
    fix p
    have expanded: "?g*ramified_weight l ?r ?s p=(?g*?r)*fst p+int l*(?g*?s)*int(snd p)"
      by (simp add: ramified_weight_def algebra_simps)
    have transported: "?g*ramified_weight l ?r ?s p=R*fst p+int l*S*int(snd p)"
      using expanded by (simp only: Re[symmetric] Se[symmetric])
    have scaled: "?g*ramified_weight l ?r ?s p=ramified_weight l R S p"
      using transported by (simp only: ramified_weight_def)
    show "ramified_weight l R S p=?g*ramified_weight l ?r ?s p"
      by (rule scaled[symmetric])
  qed
  have Pbound: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l ?r ?s p\<le>ramified_weight l ?r ?s E"
    using Pupper g by (simp only: scale; auto simp: mult_le_cancel_left_pos)
  have Qbound: "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l ?r ?s q\<le>ramified_weight l ?r ?s F"
    using Qupper g by (simp only: scale; auto simp: mult_le_cancel_left_pos)
  have Etop: "ramified_weight l ?r ?s E=ramified_weight_deg l ?r ?s P"
    by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use E Pbound in auto)
  have Ftop: "ramified_weight l ?r ?s F=ramified_weight_deg l ?r ?s Q"
    by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use F Qbound in auto)
  have gnz: "?g\<noteq>0" using g by arith
  have scaled_Ptie: "?g*ramified_weight l ?r ?s BP=?g*ramified_weight l ?r ?s E"
    using Ptie by (simp only: scale)
  have scaled_Qtie: "?g*ramified_weight l ?r ?s BQ=?g*ramified_weight l ?r ?s F"
    using Qtie by (simp only: scale)
  have BPE: "ramified_weight l ?r ?s BP=ramified_weight l ?r ?s E"
    using scaled_Ptie by (simp only: mult_left_cancel[OF gnz])
  have BQF: "ramified_weight l ?r ?s BQ=ramified_weight l ?r ?s F"
    using scaled_Qtie by (simp only: mult_left_cancel[OF gnz])
  have BPtop: "ramified_weight l ?r ?s BP=ramified_weight_deg l ?r ?s P"
    by (rule trans[OF BPE Etop])
  have BQtop: "ramified_weight l ?r ?s BQ=ramified_weight_deg l ?r ?s Q"
    by (rule trans[OF BQF Ftop])
  show ?thesis
    apply (rule exI[where x="?r"])
    apply (rule exI[where x="?s"])
    apply (rule exI[where x="?g"])
    apply (intro conjI)
            apply (rule g)
           apply (rule Re)
          apply (rule Se)
         apply (rule direction)
        apply (rule r)
       apply (rule Etop)
      apply (rule Ftop)
     apply (rule BPtop)
    apply (rule BQtop)
    done
qed
lemma ramified_common_rational_tilt_primitive_face:
  assumes l: "0<l" and rho: "0<rho"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and early: "t<(of_nat l*of_int(rho+sigma)::rat)"
    and E: "E\<in>ramified_pbw_support l P" and F: "F\<in>ramified_pbw_support l Q"
    and BP: "BP\<in>ramified_pbw_support l P" and BQ: "BQ\<in>ramified_pbw_support l Q"
    and Eweight: "ramified_weight l rho sigma E=VP" and Fweight: "ramified_weight l rho sigma F=VQ"
    and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
      (of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd E)"
    and Qfirst: "\<And>p. p\<in>ramified_pbw_support l Q \<Longrightarrow>
      (of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)\<le>of_int VQ-t*of_nat(snd F)"
    and BPtie: "(of_int(ramified_weight l rho sigma BP)::rat)-t*of_nat(snd BP)=of_int VP-t*of_nat(snd E)"
    and BQtie: "(of_int(ramified_weight l rho sigma BQ)::rat)-t*of_nat(snd BQ)=of_int VQ-t*of_nat(snd F)"
  shows "\<exists>r s::int. is_direction r s \<and> 0<r \<and>
    ramified_weight l r s E=ramified_weight_deg l r s P \<and>
    ramified_weight l r s F=ramified_weight_deg l r s Q \<and>
    ramified_weight l r s BP=ramified_weight_deg l r s P \<and>
    ramified_weight l r s BQ=ramified_weight_deg l r s Q"
proof -
  obtain R S where R: "0<R" and positive: "0<R+S"
    and Pbound: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l R S p\<le>ramified_weight l R S E"
    and Qbound: "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l R S q\<le>ramified_weight l R S F"
    and Etop: "ramified_weight l R S E=ramified_weight_deg l R S P"
    and Ftop: "ramified_weight l R S F=ramified_weight_deg l R S Q"
    and BPtop: "ramified_weight l R S BP=ramified_weight_deg l R S P"
    and BQtop: "ramified_weight l R S BQ=ramified_weight_deg l R S Q"
    using ramified_common_rational_tilt_integral_face[
      OF l rho P Q early E F BP BQ Eweight Fweight Pfirst Qfirst BPtie BQtie] by blast
  have Ptie: "ramified_weight l R S BP=ramified_weight l R S E" using BPtop Etop by simp
  have Qtie: "ramified_weight l R S BQ=ramified_weight l R S F" using BQtop Ftop by simp
  show ?thesis using ramified_common_integral_face_primitive[OF l R positive P Q E F _ _ Ptie Qtie]
    Pbound Qbound by blast
qed


lemma ramified_face_grade_min_of_order_max:
 fixes E p::"int\<times>nat"
 assumes l: "0<l" and r: "0<r" and positive: "0<r+s"
 and face: "ramified_weight l r s p=ramified_weight l r s E"
 and order: "snd p\<le>snd E"
 shows "fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
proof -
 have faceExpr: "r*fst p+int l*s*int(snd p)=r*fst E+int l*s*int(snd E)"
   using face by (simp only: ramified_weight_def)
 have zero: "(r*fst p+int l*s*int(snd p))-(r*fst E+int l*s*int(snd E))=0"
   by (simp only: faceExpr diff_self)
 have identity: "r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))-
 (int l*(r+s))*(int(snd E)-int(snd p))=
 (r*fst p+int l*s*int(snd p))-(r*fst E+int l*s*int(snd E))"
   by (simp add: algebra_simps)
 have factor: "r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))=
 (int l*(r+s))*(int(snd E)-int(snd p))" using identity zero by linarith
 have left: "0\<le>int l*(r+s)" using l positive by simp
 have right: "0\<le>int(snd E)-int(snd p)" using order by simp
 have product: "0\<le>(int l*(r+s))*(int(snd E)-int(snd p))"
   by (rule mult_nonneg_nonneg[OF left right])
 have scaled_grade: "0\<le>r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))"
   using product by (simp only: factor)
 have grade: "0\<le>(fst p-int l*int(snd p))-(fst E-int l*int(snd E))"
   using scaled_grade r by (simp only: zero_le_mult_iff; arith)
 show ?thesis using grade by arith
qed

lemma ramified_first_tilt_old_start_min_grade:
 fixes E::"int\<times>nat" and t::rat
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 and t: "0<t" and Eweight: "ramified_weight l rho sigma E=V"
 and oldTop: "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow>ramified_weight l rho sigma p\<le>V"
 and g: "0<g" and R: "rationalTiltRho l rho t=g*r" and S: "rationalTiltSigma l sigma t=g*s"
 and r: "0<r" and positive: "0<r+s"
 and Et: "ramified_weight l r s E=ramified_weight_deg l r s T"
 shows "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l r s p=ramified_weight_deg l r s T \<longrightarrow>
 fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
proof (intro ballI impI)
 fix p assume p: "p\<in>ramified_pbw_support l T" and top: "ramified_weight l r s p=ramified_weight_deg l r s T"
 have equal: "ramified_weight l r s p=ramified_weight l r s E" using top Et by simp
 have scale: "\<And>q. ramified_weight l (rationalTiltRho l rho t)(rationalTiltSigma l sigma t)q=g*ramified_weight l r s q"
   by (simp only: R S ramified_weight_def; simp add: algebra_simps)
 have tilted: "ramified_weight l (rationalTiltRho l rho t)(rationalTiltSigma l sigma t)p=
 ramified_weight l (rationalTiltRho l rho t)(rationalTiltSigma l sigma t)E"
   by (simp only: scale equal)
 have cast: "(of_int(ramified_weight l (rationalTiltRho l rho t)(rationalTiltSigma l sigma t)p)::rat)=
 of_int(ramified_weight l (rationalTiltRho l rho t)(rationalTiltSigma l sigma t)E)"
   by (rule arg_cong[OF tilted])
 have denominator: "0<snd(quotient_of t)" by (rule quotient_of_denom_pos')
 have nonzero: "(of_nat l*of_int(snd(quotient_of t))::rat)\<noteq>0" using l denominator by simp
 have tie: "(of_int(ramified_weight l rho sigma p)::rat)-t*of_nat(snd p)=of_int V-t*of_nat(snd E)"
   using cast nonzero by (simp only: rationalTilt_weight_scale; simp add: Eweight)
 have order: "snd p\<le>snd E"
   by (rule finiteSupport_tilted_face_order_le_old_start[where S="ramified_pbw_support l T"
 and w="ramified_weight l rho sigma" and V=V and M="snd E" and t=t and p=p, OF t oldTop p tie])
 show "fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
   by (rule ramified_face_grade_min_of_order_max[OF l r positive equal order])
qed
end
