theory Homogeneous_Root
 imports "Poisson_Fixed_Point_Weight"
begin

lemma signedEuler_coeff_explicit:
 fixes F::"complex bivariate"
 shows "biv_coeff (smult [:of_int rho:] (biv_monom 1 1 0*biv_dx F)+
   smult [:of_int sigma:] (biv_monom 1 0 1*biv_dy F)) i j =
   of_int (pair_weight rho sigma (i,j))*biv_coeff F i j"
 by (simp only: fixedPointEuler_def[symmetric] fixedPointEuler_coeff)

lemma homogeneous_root_euler_power_cleared:
 fixes S::"complex bivariate"
 shows "S*fixedPointEuler rho sigma (S^d)=
   of_nat d*S^d*fixedPointEuler rho sigma S"
proof (induction d)
 case 0
 have Euler_one: "fixedPointEuler rho sigma (1::complex bivariate)=0"
 proof (rule biv_eqI)
   fix i j
   show "biv_coeff(fixedPointEuler rho sigma (1::complex bivariate)) i j=biv_coeff 0 i j"
     by (simp only: fixedPointEuler_coeff; cases i; cases j) (simp_all add: biv_coeff_def pair_weight_def)
 qed
 then show ?case by simp
next
 case (Suc d)
 have expand: "S*fixedPointEuler rho sigma (S^Suc d)=
   S*(fixedPointEuler rho sigma (S^d)*S+S^d*fixedPointEuler rho sigma S)"
   by (simp only: power_Suc fixedPointEuler_mul; algebra)
 have multiplied: "(S*fixedPointEuler rho sigma (S^d))*S=
   (of_nat d*S^d*fixedPointEuler rho sigma S)*S"
   by (rule arg_cong[OF Suc.IH])
 have "S*fixedPointEuler rho sigma (S^Suc d)=
   (S*fixedPointEuler rho sigma (S^d))*S+S*S^d*fixedPointEuler rho sigma S"
   by (simp only: expand; algebra)
 also have "...=(of_nat d*S^d*fixedPointEuler rho sigma S)*S+
   S*S^d*fixedPointEuler rho sigma S"
   by (simp only: multiplied)
 also have "...=of_nat(Suc d)*S^Suc d*fixedPointEuler rho sigma S"
   by (simp only: of_nat_Suc power_Suc; algebra)
 finally show ?case .
qed

lemma weighted_homogeneous_root_of_power:
 fixes S::"complex bivariate"
 assumes S: "S\<noteq>0" and d: "0<d"
 and power: "weighted_homogeneous rho sigma N (S^d)"
 shows "\<exists>m::int. weighted_homogeneous rho sigma m S \<and> N=int d*m"
proof -
 have Euler: "fixedPointEuler rho sigma (S^d)=[:[:of_int N:]:]*S^d"
   using fixedPointEuler_of_homogeneous[OF power]
   by (simp only: joseph_smult_constant)
 have equality: "S*([:[:of_int N:]:]*S^d)=of_nat d*S^d*fixedPointEuler rho sigma S"
   using homogeneous_root_euler_power_cleared[of S rho sigma d] by (simp only: Euler)
 have expanded: "S^d*(of_nat d*fixedPointEuler rho sigma S-[:[:of_int N:]:]*S)=
   of_nat d*S^d*fixedPointEuler rho sigma S-S*([:[:of_int N:]:]*S^d)"
   by (simp add: algebra_simps)
 have product: "S^d*(of_nat d*fixedPointEuler rho sigma S-[:[:of_int N:]:]*S)=0"
   using expanded by (simp only: equality diff_self)
 have cancel: "of_nat d*fixedPointEuler rho sigma S=[:[:of_int N:]:]*S"
   using product S by simp
 have weight: "int d*pair_weight rho sigma e=N" if "e\<in>biv_support S" for e
 proof -
   have nz: "biv_coeff S (fst e)(snd e)\<noteq>0" using that by (simp add: biv_support_def)
   have coeff: "biv_coeff (of_nat d*fixedPointEuler rho sigma S) (fst e)(snd e)=
     biv_coeff ([:[:of_int N:]:]*S) (fst e)(snd e)" using cancel by simp
   have cast: "(of_nat d::complex)* of_int(pair_weight rho sigma e)= of_int N"
     using coeff nz by (simp add: of_nat_poly fixedPointEuler_coeff)
   have natural_cast: "(of_int(int d)::complex)=of_nat d" by simp
   have "(of_int(int d*pair_weight rho sigma e)::complex)= of_int N"
     using cast by (simp only: of_int_mult natural_cast)
   then show ?thesis by (simp only: of_int_eq_iff)
 qed
 obtain e where e: "e\<in>biv_support S" using S by (metis biv_support_empty_iff all_not_in_conv)
 let ?m="pair_weight rho sigma e"
 have hom: "weighted_homogeneous rho sigma ?m S"
   unfolding weighted_homogeneous_def
 proof (intro ballI)
   fix f assume f: "f\<in>biv_support S"
   have "int d*pair_weight rho sigma f=int d*?m" using weight[OF f] weight[OF e] by simp
   then show "pair_weight rho sigma f=?m" using d by simp
 qed
 show ?thesis by (intro exI[of _ ?m] conjI hom) (use weight[OF e] in simp)
qed

end
