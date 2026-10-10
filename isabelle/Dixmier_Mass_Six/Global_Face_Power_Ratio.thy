theory Global_Face_Power_Ratio
 imports "Common_Power_Root" "Homogeneous_Root"
   "Affine_Bracket_Exclusion"
   "Homogeneous_Power_Ratio"
begin

lemma global_leading_form_nonzero_of_positive_degree:
 fixes T::"complex poly_operator"
 assumes positive: "0<v_degree rho sigma T"
 shows "leading_form rho sigma T\<noteq>0"
proof -
 have degree: "weighted_degree rho sigma (pbw_symbol T)=bot.Value(v_degree rho sigma T)"
   using positive by (cases "weighted_degree rho sigma (pbw_symbol T)")
     (simp_all add: v_degree_def)
 show ?thesis unfolding leading_form_def by (rule weighted_top_component_nonzero[OF degree])
qed

lemma counterexample_leading_faces_power_ratio:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "\<exists>m omega::nat. \<exists>c::complex. 0<m \<and> 0< omega \<and> c\<noteq>0 \<and>
 int m=v_degree rho sigma P \<and> int omega=v_degree rho sigma Q \<and>
 (leading_form rho sigma Q)^m=[:[:c:]:]*(leading_form rho sigma P)^omega"
proof -
 have Ppos: "0<v_degree rho sigma P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have swap: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have Qpos: "0<v_degree rho sigma Q" by (rule counterexample_vDeg_pos_all_directions[OF swap direction])
 let ?m="nat(v_degree rho sigma P)" let ?omega="nat(v_degree rho sigma Q)"
 have m: "0<?m" and omega: "0<?omega" using Ppos Qpos by simp_all
 have mcast: "int ?m=v_degree rho sigma P" and ocast: "int ?omega=v_degree rho sigma Q"
   using Ppos Qpos by simp_all
 have Phom: "weighted_homogeneous rho sigma (int ?m) (leading_form rho sigma P)"
   unfolding mcast leading_form_def by (rule weighted_component_homogeneous)
 have Qhom: "weighted_homogeneous rho sigma (int ?omega) (leading_form rho sigma Q)"
   unfolding ocast leading_form_def by (rule weighted_component_homogeneous)
 have Pnz: "leading_form rho sigma P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree[OF Ppos])
 have Qnz: "leading_form rho sigma Q\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree[OF Qpos])
 have zero: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0"
   by (rule counterexample_leadingPoisson_zero_all_directions[OF pair direction])
 obtain c where c: "c\<noteq>0" and power: "(leading_form rho sigma Q)^?m=[:[:c:]:]*(leading_form rho sigma P)^?omega"
   using homogeneous_poisson_power_ratio[OF m omega Qnz Pnz Qhom Phom zero] by auto
 show ?thesis by (intro exI[of _ ?m] exI[of _ ?omega] exI[of _ c])
   (use m omega c mcast ocast power in blast)
qed

lemma counterexample_leading_faces_prime_multiplicity_ratio:
 fixes P Q::"complex poly_operator" and p::"complex bivariate"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma" and prime: "prime_elem p"
 shows "\<exists>m omega::nat. 0<m \<and> 0< omega \<and> int m=v_degree rho sigma P \<and>
 int omega=v_degree rho sigma Q \<and> m*multiplicity p (leading_form rho sigma Q)=
 omega*multiplicity p (leading_form rho sigma P)"
proof -
 obtain m omega c where m: "0<m" and omega: "0< omega" and c: "c\<noteq>0"
 and mc: "int m=v_degree rho sigma P" and oc: "int omega=v_degree rho sigma Q"
 and power: "(leading_form rho sigma Q)^m=[:[:c:]:]*(leading_form rho sigma P)^omega"
   using counterexample_leading_faces_power_ratio[OF pair direction] by auto
 have Pnz: "leading_form rho sigma P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use m mc in simp)
 have Qnz: "leading_form rho sigma Q\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use omega oc in simp)
 have eq: "m*multiplicity p (leading_form rho sigma Q)= omega*multiplicity p (leading_form rho sigma P)"
   by (rule multiplicity_power_ratio[OF Qnz Pnz c power prime])
 show ?thesis by (intro exI[of _ m] exI[of _ omega]) (use m omega mc oc eq in blast)
qed

lemma counterexample_leading_faces_common_root_of_coprime_ratio:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and n: "0<n" and d: "0<d" and cop: "coprime d n"
 and ratio: "nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
 shows "\<exists>S nu mu. S\<noteq>0 \<and> nu\<noteq>0 \<and> mu\<noteq>0 \<and>
 leading_form rho sigma P=[:[:nu:]:]*S^d \<and> leading_form rho sigma Q=[:[:mu:]:]*S^n"
proof -
 obtain m omega c where m: "0<m" and omega: "0< omega" and c: "c\<noteq>0"
 and mc: "int m=v_degree rho sigma P" and oc: "int omega=v_degree rho sigma Q"
 and power: "(leading_form rho sigma Q)^m=[:[:c:]:]*(leading_form rho sigma P)^omega"
   using counterexample_leading_faces_power_ratio[OF pair direction] by auto
 have mn: "m=nat(v_degree rho sigma P)" and on: "omega=nat(v_degree rho sigma Q)"
   using mc oc by (metis nat_int)+
 have reduced: "omega*d=m*n" using ratio by (simp only: mn on)
 have Pnz: "leading_form rho sigma P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use m mc in simp)
 have Qnz: "leading_form rho sigma Q\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use omega oc in simp)
 show ?thesis by (rule bivariate_common_root_of_coprime_ratio[OF Qnz Pnz c reduced m omega n d cop power])
qed

lemma counterexample_leading_faces_homogeneous_common_root:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and n: "0<n" and d: "0<d" and cop: "coprime d n"
 and ratio: "nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
 shows "\<exists>S nu mu r. S\<noteq>0 \<and> nu\<noteq>0 \<and> mu\<noteq>0 \<and>
 weighted_homogeneous rho sigma r S \<and> v_degree rho sigma P=int d*r \<and>
 leading_form rho sigma P=[:[:nu:]:]*S^d \<and> leading_form rho sigma Q=[:[:mu:]:]*S^n"
proof -
 obtain S nu mu where S: "S\<noteq>0" and nu: "nu\<noteq>0" and mu: "mu\<noteq>0"
 and Pshape: "leading_form rho sigma P=[:[:nu:]:]*S^d"
 and Qshape: "leading_form rho sigma Q=[:[:mu:]:]*S^n"
   using counterexample_leading_faces_common_root_of_coprime_ratio[OF pair direction n d cop ratio] by auto
 have support: "biv_support(leading_form rho sigma P)=biv_support(S^d)"
   by (simp add: Pshape biv_support_def biv_coeff_def nu)
 have Phom: "weighted_homogeneous rho sigma (v_degree rho sigma P) (leading_form rho sigma P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have powerhom: "weighted_homogeneous rho sigma (v_degree rho sigma P) (S^d)"
   using Phom support by (simp only: weighted_homogeneous_def)
 obtain r where hom: "weighted_homogeneous rho sigma r S" and weight: "v_degree rho sigma P=int d*r"
   using weighted_homogeneous_root_of_power[OF S d powerhom] by auto
 show ?thesis by (intro exI[of _ S] exI[of _ nu] exI[of _ mu] exI[of _ r])
   (use S nu mu hom weight Pshape Qshape in blast)
qed

lemma global_reduced_face_ratio_positive:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and cop: "coprime d n"
 and ratio: "nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
 shows "0<n \<and> 0<d"
proof -
 have Ppos: "0<nat(v_degree rho sigma P)"
   using counterexample_vDeg_pos_all_directions[OF pair direction] by simp
 have Qpos: "0<nat(v_degree rho sigma Q)"
   using counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction] by simp
 have dpos: "0<d"
 proof (rule ccontr)
   assume "\<not>0<d" then have dz: "d=0" by simp
   have nz: "n=0" using ratio Ppos by (simp add: dz)
   show False using cop by (simp add: dz nz)
 qed
 have npos: "0<n"
 proof (rule ccontr)
   assume "\<not>0<n" then have nz: "n=0" by simp
   have dz: "d=0" using ratio Qpos by (simp add: nz)
   show False using cop by (simp add: dz nz)
 qed
 show ?thesis using npos dpos by blast
qed

lemma counterexample_first_leading_face_power_of_coprime_ratio:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and cop: "coprime d n"
 and ratio: "nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
 shows "\<exists>nu S. nu\<noteq>0 \<and> leading_form rho sigma P=[:[:nu:]:]*S^d"
proof -
 have pos: "0<n \<and> 0<d" by (rule global_reduced_face_ratio_positive[OF pair direction cop ratio])
 have npos: "0<n" and dpos: "0<d" using pos by auto
 show ?thesis
   using counterexample_leading_faces_common_root_of_coprime_ratio[OF pair direction npos dpos cop ratio] by blast
qed

lemma counterexample_both_leading_faces_powers_of_coprime_ratio:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and cop: "coprime d n"
 and ratio: "nat(v_degree rho sigma Q)*d=nat(v_degree rho sigma P)*n"
 shows "(\<exists>nu S. nu\<noteq>0 \<and> leading_form rho sigma P=[:[:nu:]:]*S^d) \<and>
 (\<exists>mu T. mu\<noteq>0 \<and> leading_form rho sigma Q=[:[:mu:]:]*T^n)"
proof -
 have pos: "0<n \<and> 0<d" by (rule global_reduced_face_ratio_positive[OF pair direction cop ratio])
 have npos: "0<n" and dpos: "0<d" using pos by auto
 show ?thesis
   using counterexample_leading_faces_common_root_of_coprime_ratio[OF pair direction npos dpos cop ratio] by blast
qed

end
