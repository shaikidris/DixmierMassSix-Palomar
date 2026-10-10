theory GGV_Cut_Corner_Proved
 imports "Finite_Cut_Corner_Descent"
   "Cut_Corner_Normalized_Configuration"
begin

lemma ggv_cut_corner_proved:
 fixes P Q::"complex poly_operator" and rho sigma::int and u v n d h::nat
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and sigma: "sigma\<le>0"
 and Pdir: "in_direction rho sigma P" and Qdir: "in_direction rho sigma Q"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and Pnd: "\<not>v_degree rho sigma P dvd v_degree rho sigma Q"
 and Qnd: "\<not>v_degree rho sigma Q dvd v_degree rho sigma P"
 and Pneg: "\<exists>e\<in>biv_support(leading_form rho sigma P). pair_grade e<0"
 and Qneg: "\<exists>e\<in>biv_support(leading_form rho sigma Q). pair_grade e<0"
 and point: "(u,v)\<in>biv_support(leading_form rho sigma P)"
 and maximum: "\<forall>e\<in>biv_support(leading_form rho sigma P). pair_grade e\<le>pair_grade(u,v)"
 and ratio: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n"
 and n: "1<n" and d: "1<d" and cop: "coprime n d" and h: "2\<le>h"
 shows "\<not>(((of_nat u+((of_nat v::rat)- of_nat(max_root_mult(cut_poly rho sigma P))) * of_int sigma/ of_int rho)/ of_nat d=
   of_nat h-1/ of_int rho) \<and> (of_nat(max_root_mult(cut_poly rho sigma P))::rat)/ of_nat d= of_nat h)"
proof
 assume corner: "((of_nat u+((of_nat v::rat)- of_nat(max_root_mult(cut_poly rho sigma P))) * of_int sigma/ of_int rho)/ of_nat d=
   of_nat h-1/ of_int rho) \<and> (of_nat(max_root_mult(cut_poly rho sigma P))::rat)/ of_nat d= of_nat h"
 let ?l="nat rho"
 have l: "0<?l" and index: "int ?l=rho" using rho by simp_all
 have divides: "rho dvd int ?l" by (simp only: index dvd_refl)
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast+
 obtain c r s where newdir: "is_direction r s" and r: "0<r" and s: "s<0"
 and data: "let U=ramified_cut_aut ?l rho sigma c (polynomial_ramified_lift ?l P);
      V=ramified_cut_aut ?l rho sigma c (polynomial_ramified_lift ?l Q);
      N=rootMultiplicity c (cut_poly rho sigma Q);
      E=(int d*(int h*int ?l-1),d*h);
      F=((int ?l div rho)*v_degree rho sigma Q-ramified_cut_exponent ?l rho sigma*int N,N)
 in E\<in>ramified_pbw_support ?l U \<and> F\<in>ramified_pbw_support ?l V \<and>
    ramified_weight ?l r s E=ramified_weight_deg ?l r s U \<and>
    ramified_weight ?l r s F=ramified_weight_deg ?l r s V \<and>
    0<ramified_weight_deg ?l r s U \<and> 0<ramified_weight_deg ?l r s V \<and>
    ramified_weight_deg ?l r s V*int d=ramified_weight_deg ?l r s U*int n \<and>
    int ?l*(r+s)<ramified_weight_deg ?l r s U+ramified_weight_deg ?l r s V \<and>
    laurent_comp V U-laurent_comp U V=id \<and>
    (\<forall>p\<in>ramified_pbw_support ?l U. ramified_weight ?l r s p=ramified_weight_deg ?l r s U \<longrightarrow>
      fst E-int ?l*int(snd E)\<le>fst p-int ?l*int(snd p)) \<and>
    (\<forall>q\<in>ramified_pbw_support ?l V. ramified_weight ?l r s q=ramified_weight_deg ?l r s V \<longrightarrow>
      fst F-int ?l*int(snd F)\<le>fst q-int ?l*int(snd q)) \<and>
    (\<exists>BP\<in>ramified_pbw_support ?l U. snd BP<d*h \<and> ramified_weight ?l r s BP=ramified_weight_deg ?l r s U)"
   using counterexample_normalized_cut_corner_configuration[OF l pair direction rho sigma index Pdir Qdir threshold d n h ratio cop Pneg point corner]
   by (simp only: Let_def; blast)
 let ?U="ramified_cut_aut ?l rho sigma c (polynomial_ramified_lift ?l P)"
 let ?V="ramified_cut_aut ?l rho sigma c (polynomial_ramified_lift ?l Q)"
 let ?E="(int d*(int h*int ?l-1),d*h)"
 let ?F="((int ?l div rho)*v_degree rho sigma Q-ramified_cut_exponent ?l rho sigma*int(rootMultiplicity c (cut_poly rho sigma Q)),rootMultiplicity c (cut_poly rho sigma Q))"
 have U: "?U\<in>ramified_operator_algebra ?l" and V: "?V\<in>ramified_operator_algebra ?l"
   by (rule ramified_cut_aut_mem[OF l polynomial_ramified_lift_carrier])+
 have Esupport: "?E\<in>ramified_pbw_support ?l ?U" and Fsupport: "?F\<in>ramified_pbw_support ?l ?V"
 and Et: "ramified_weight ?l r s ?E=ramified_weight_deg ?l r s ?U"
 and Ft: "ramified_weight ?l r s ?F=ramified_weight_deg ?l r s ?V"
 and Upos: "0<ramified_weight_deg ?l r s ?U" and Vpos: "0<ramified_weight_deg ?l r s ?V"
 and newratio: "ramified_weight_deg ?l r s ?V*int d=ramified_weight_deg ?l r s ?U*int n"
 and strict: "int ?l*(r+s)<ramified_weight_deg ?l r s ?U+ramified_weight_deg ?l r s ?V"
 and comm: "laurent_comp ?V ?U-laurent_comp ?U ?V=id"
 and Emin: "\<And>p. p\<in>ramified_pbw_support ?l ?U \<Longrightarrow> ramified_weight ?l r s p=ramified_weight_deg ?l r s ?U \<Longrightarrow>
   fst ?E-int ?l*int(snd ?E)\<le>fst p-int ?l*int(snd p)"
 and Fmin: "\<And>q. q\<in>ramified_pbw_support ?l ?V \<Longrightarrow> ramified_weight ?l r s q=ramified_weight_deg ?l r s ?V \<Longrightarrow>
   fst ?F-int ?l*int(snd ?F)\<le>fst q-int ?l*int(snd q)"
   using data by (simp only: Let_def; blast)+
 have newsum: "0<r+s" using newdir by (simp add: is_direction_def)
 have Uend: "degree(ramified_top_face_polynomial ?l r s ?U)=snd ?E \<and> ramified_pbw_top_laurent ?l ?U (snd ?E)=fst ?E"
   by (rule ramified_min_grade_top_canonical_ending[OF l U r newsum Esupport Et Emin])
 have Vend: "degree(ramified_top_face_polynomial ?l r s ?V)=snd ?F \<and> ramified_pbw_top_laurent ?l ?V (snd ?F)=fst ?F"
   by (rule ramified_min_grade_top_canonical_ending[OF l V r newsum Fsupport Ft Fmin])
 have Ul: "laurent_linear ?U" and Vl: "laurent_linear ?V"
   using ramified_operator_algebra_linear[OF U] ramified_operator_algebra_linear[OF V] by blast+
 have one_nonzero: "(id::laurent_operator)\<noteq>0"
   by (intro notI) (drule fun_cong[where x="1::ramified_laurent"]; simp)
 have Unz: "?U\<noteq>0" and Vnz: "?V\<noteq>0" using comm Ul Vl one_nonzero
   by (auto simp: laurent_comp_zero_left laurent_comp_zero_right)
 have positive_threshold: "0<ramified_weight_deg ?l r s ?U+ramified_weight_deg ?l r s ?V-int ?l*(r+s)" using strict by arith
 have proportion: "int n*fst ?E=int d*fst ?F \<and> n*snd ?E=d*snd ?F"
   using ramified_exact_pair_canonical_ends_proportional[OF l r newsum U V Unz Vnz comm Upos Vpos positive_threshold newratio]
     Uend Vend by (simp only: fst_conv snd_conv; auto)
 have dp: "0<d" and d2: "2\<le>d" and n2: "2\<le>n" using d n by arith+
 have mate: "fst ?F=int n*(int ?l*int h-1) \<and> snd ?F=n*h"
   by (rule ramified_normalized_corner_proportion_mate_coordinates[OF dp])
     (use proportion in \<open>auto simp: mult.commute\<close>)
 let ?a="\<lparr>cut_rho=rho,cut_sigma=sigma,cut_root=c\<rparr>"
 have oldsum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have admissible: "admissible_ramified_cut ?l ?a" using rho divides sigma oldsum by (simp add: admissible_ramified_cut_def)
 have history: "admissible_ramified_history ?l [?a]" using admissible by (simp add: admissible_ramified_history_def)
 have imageU: "finite_cut_image ?l [?a] P=?U" and imageV: "finite_cut_image ?l [?a] Q=?V"
   by (simp_all add: finite_cut_image_def)
 obtain B where B: "B\<in>ramified_pbw_support ?l ?U" and lower: "snd B<d*h"
 and Bt: "ramified_weight ?l r s B=ramified_weight_deg ?l r s ?U" using data by (simp only: Let_def; blast)
 have upper: "\<forall>p\<in>ramified_pbw_support ?l ?U. ramified_weight ?l r s p\<le>ramified_weight_deg ?l r s ?U"
   using ramified_weight_deg_upper by blast
 have Bdata: "snd B\<in>Poly_Mapping.keys(ramified_pbw_coeffs ?l ?U) \<and>
   ramified_pbw_top_laurent ?l ?U (snd B)=fst B \<and>
   ramified_weight ?l r s (ramified_pbw_top_laurent ?l ?U (snd B),snd B)=ramified_weight_deg ?l r s ?U"
   by (rule ramified_face_point_top_laurent_at_order[OF r B Bt upper])
 have Bkey: "snd B\<in>Poly_Mapping.keys(ramified_pbw_coeffs ?l ?U)"
   by (rule conjunct1[OF Bdata])
 have Bweight: "r*ramified_pbw_top_laurent ?l ?U (snd B)+int ?l*s*int(snd B)=ramified_weight_deg ?l r s ?U"
   using conjunct2[OF conjunct2[OF Bdata]] by (simp only: ramified_weight_def fst_conv snd_conv)
 have Bpoly: "snd B\<in>polynomial_support(ramified_top_face_polynomial ?l r s ?U)"
   by (rule iffD2[OF ramified_top_face_polynomial_mem_support_iff])
     (rule conjI[OF Bkey Bweight])
 have genuine: "\<exists>j\<in>polynomial_support(ramified_top_face_polynomial ?l r s ?U). j\<noteq>degree(ramified_top_face_polynomial ?l r s ?U)"
   by (rule bexI[of _ "snd B"]) (use Bpoly lower Uend in auto)
 have Ffirst: "fst ?F=int n*(int ?l*int h-1)" and Fsecond: "snd ?F=n*h"
   using mate by blast+
 have Unormalized: "degree(ramified_top_face_polynomial ?l r s ?U)=d*h \<and>
   ramified_pbw_top_laurent ?l ?U (d*h)=int d*(int ?l*int h-1)"
   using Uend by (simp only: fst_conv snd_conv mult.commute)
 have Vnormalized: "degree(ramified_top_face_polynomial ?l r s ?V)=n*h \<and>
   ramified_pbw_top_laurent ?l ?V (n*h)=int n*(int ?l*int h-1)"
   using Vend by (simp only: Ffirst Fsecond)
 have s_nonpos: "s\<le>0" using s by arith
 have state: "finite_cut_corner_state ?l P Q n d h [?a] r s"
   using history newdir r s_nonpos Upos Vpos newratio Unormalized Vnormalized genuine
   by (simp only: finite_cut_corner_state_def imageU imageV; blast)
 have cop': "coprime d n" using cop by (simp only: coprime_commute)
 show False by (rule finiteCutCornerState_impossible[OF l P Q exact d2 n2 h cop' state])
qed

end
