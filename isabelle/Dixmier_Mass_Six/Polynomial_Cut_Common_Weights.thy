theory Polynomial_Cut_Common_Weights
 imports Polynomial_Cut_Common_Direction Ramified_Common_Face_Ratio
begin

lemma exactPair_maxRoot_cut_exists_common_face_positive_ratio_and_min_grade:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
 and exact: "op_comp Q P-op_comp P Q=id"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and weights: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and grade: "(int l div rho)*v_degree rho sigma P-(ramified_cut_exponent l rho sigma+int l)*
 int(max_root_mult(cut_poly rho sigma P))<0"


 shows "\<exists>c r s. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 is_direction r s \<and>0<r \<and>(sigma\<le>0 \<longrightarrow>s<0) \<and>
 (let U=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P);
 V=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q);
 M=rootMultiplicity c(cut_poly rho sigma P); N=rootMultiplicity c(cut_poly rho sigma Q);
 E=((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M);
 F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in ramified_weight l r s E=ramified_weight_deg l r s U \<and>
 ramified_weight l r s F=ramified_weight_deg l r s V \<and>
 0<ramified_weight_deg l r s U \<and>0<ramified_weight_deg l r s V \<and>
 ramified_weight_deg l r s V*int d=ramified_weight_deg l r s U*int n \<and>
 fst E-int l*int(snd E)<0 \<and>fst F-int l*int(snd F)<0 \<and>
 (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l r s p=ramified_weight_deg l r s U \<longrightarrow>
 fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
 (\<forall>q\<in>ramified_pbw_support l V. ramified_weight l r s q=ramified_weight_deg l r s V \<longrightarrow>
 fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)) \<and>
 (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and>ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
 (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and>ramified_weight l r s BQ=ramified_weight_deg l r s V))"
proof -
 let ?LP="polynomial_ramified_lift l P" let ?LQ="polynomial_ramified_lift l Q"
 let ?U="\<lambda>c. ramified_cut_aut l rho sigma c ?LP" let ?V="\<lambda>c. ramified_cut_aut l rho sigma c ?LQ"
 let ?M="\<lambda>c. rootMultiplicity c(cut_poly rho sigma P)" let ?N="\<lambda>c. rootMultiplicity c(cut_poly rho sigma Q)"
 let ?rP="(int l div rho)*v_degree rho sigma P" let ?rQ="(int l div rho)*v_degree rho sigma Q"
 let ?k="ramified_cut_exponent l rho sigma"
 let ?E="\<lambda>c. (?rP-?k*int(?M c),?M c)" let ?F="\<lambda>c. (?rQ-?k*int(?N c),?N c)"
 obtain c r s where root: "poly(cut_poly rho sigma P)c=0" and maximum: "?M c=max_root_mult(cut_poly rho sigma P)"
 and dir: "is_direction r s" and r: "0<r" and sNeg: "sigma\<le>0 \<longrightarrow>s<0"
 and Et: "ramified_weight l r s(?E c)=ramified_weight_deg l r s(?U c)"
 and Ft: "ramified_weight l r s(?F c)=ramified_weight_deg l r s(?V c)"
 and Pmin: "\<forall>p\<in>ramified_pbw_support l(?U c). ramified_weight l r s p=ramified_weight_deg l r s(?U c) \<longrightarrow>
 fst(?E c)-int l*int(snd(?E c))\<le>fst p-int l*int(snd p)"
 and Qmin: "\<forall>q\<in>ramified_pbw_support l(?V c). ramified_weight l r s q=ramified_weight_deg l r s(?V c) \<longrightarrow>
 fst(?F c)-int l*int(snd(?F c))\<le>fst q-int l*int(snd q)"
 and BP: "\<exists>BP\<in>ramified_pbw_support l(?U c). snd BP<?M c \<and>ramified_weight l r s BP=ramified_weight_deg l r s(?U c)"
 and BQ: "\<exists>BQ\<in>ramified_pbw_support l(?V c). snd BQ<?N c \<and>ramified_weight l r s BQ=ramified_weight_deg l r s(?V c)"
   using exactPair_maxRoot_cut_exists_primitive_common_face[OF l P Q direction rho divides Ppos Qpos Pface Qface exact threshold d n weights cop grade]
   unfolding Let_def by blast
 have sumOld: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have sumNew: "0<r+s" using dir by (simp add: is_direction_def)
 have Pne: "cut_poly rho sigma P\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho Pface])
 have Mpos: "0<?M c" using root Pne by (auto simp: rootMultiplicity_def order_root)
 have rootNat: "nat(v_degree rho sigma Q)*?M c=nat(v_degree rho sigma P)*?N c"
   by (rule polynomial_exact_pair_cut_root_ratio[OF l P Q rho sumOld divides Ppos Qpos exact threshold])
 have cast: "int(nat(v_degree rho sigma Q)*?M c)=int(nat(v_degree rho sigma P)*?N c)"
   by (rule arg_cong[OF rootNat])
 have rootInt: "v_degree rho sigma Q*int(?M c)=v_degree rho sigma P*int(?N c)"
   using cast Ppos Qpos by simp
 have cross: "n*?M c=d*?N c" by (rule native_reduced_root_order_cross[OF Ppos weights rootInt])
 have order: "int(snd(?E c))*int n=int(snd(?F c))*int d"
   using arg_cong[OF cross, of "\<lambda>a::nat. int a"] by (simp add: mult.commute)
 have parallel: "int(snd(?E c))*fst(?F c)=int(snd(?F c))*fst(?E c)"
   using cut_oldFace_endpoints_parallel[OF Ppos Qpos rootNat, where l=l and rho=rho and sigma=sigma] by simp
 have Ec: "?U c\<in>ramified_operator_algebra l" and Fc: "?V c\<in>ramified_operator_algebra l"
   by (rule ramified_cut_aut_mem[OF l polynomial_ramified_lift_carrier])+
 have cutExact: "laurent_comp(?V c)(?U c)-laurent_comp(?U c)(?V c)=id"
   by (rule ramified_cut_aut_exact_pair[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier
      polynomial_ramified_lift_bracket_one[OF l P Q exact]])
 have Epos: "0<snd(?E c)" using Mpos by simp
 have dpos: "0<d" and npos: "0<n" using d n by arith+
 have newWeights: "0<ramified_weight_deg l r s(?U c) \<and>0<ramified_weight_deg l r s(?V c) \<and>
 ramified_weight_deg l r s(?V c)*int d=ramified_weight_deg l r s(?U c)*int n"
   by (rule ramified_exact_pair_parallel_top_weights_positive_ratio[OF l r sumNew Ec Fc cutExact Epos parallel Et Ft dpos npos order])
 have Eg: "fst(?E c)-int l*int(snd(?E c))<0" using grade maximum by (simp add: algebra_simps)
 have Npos: "0<?N c"
 proof (rule ccontr)
   assume "\<not>0<?N c" then have zero: "?N c=0" by simp
   have "0<n*?M c" using npos Mpos by simp
   then show False using cross zero by simp
 qed
 have scale: "int(?M c)*(fst(?F c)-int l*int(?N c))=int(?N c)*(fst(?E c)-int l*int(?M c))"
   using parallel by (simp add: algebra_simps)
 have rhs: "int(?N c)*(fst(?E c)-int l*int(?M c))<0"
   by (rule mult_pos_neg) (use Npos Eg in simp_all)
 have left_negative: "int(?M c)*(fst(?F c)-int l*int(?N c))<0"
   using rhs by (simp only: scale)
 have multiplier_positive: "0<int(?M c)" using Mpos by simp
 have reduced_negative: "fst(?F c)-int l*int(?N c)<0"
   using left_negative multiplier_positive by (simp only: mult_less_0_iff; arith)
 have Fg: "fst(?F c)-int l*int(snd(?F c))<0"
   using reduced_negative by (simp only: snd_conv)
 show ?thesis
   by (rule exI[where x=c], rule exI[where x=r], rule exI[where x=s])
     (use root maximum dir r sNeg Et Ft newWeights Eg Fg Pmin Qmin BP BQ in \<open>auto simp: Let_def\<close>)
qed


lemma exactPair_maxRoot_cut_exists_common_face_positive_ratio:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
 and exact: "op_comp Q P-op_comp P Q=id"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and weights: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and grade: "(int l div rho)*v_degree rho sigma P-(ramified_cut_exponent l rho sigma+int l)*
 int(max_root_mult(cut_poly rho sigma P))<0"


 shows "\<exists>c r s. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 is_direction r s \<and>0<r \<and>(sigma\<le>0 \<longrightarrow>s<0) \<and>
 (let U=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P);
 V=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q);
 M=rootMultiplicity c(cut_poly rho sigma P); N=rootMultiplicity c(cut_poly rho sigma Q);
 E=((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M);
 F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in ramified_weight l r s E=ramified_weight_deg l r s U \<and>
 ramified_weight l r s F=ramified_weight_deg l r s V \<and>
 0<ramified_weight_deg l r s U \<and>0<ramified_weight_deg l r s V \<and>
 ramified_weight_deg l r s V*int d=ramified_weight_deg l r s U*int n \<and>
 fst E-int l*int(snd E)<0 \<and>fst F-int l*int(snd F)<0 \<and>
 (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and>ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
 (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and>ramified_weight l r s BQ=ramified_weight_deg l r s V))"
 using exactPair_maxRoot_cut_exists_common_face_positive_ratio_and_min_grade
 [OF l P Q direction rho divides Ppos Qpos Pface Qface exact threshold d n weights cop grade]
 by (auto simp: Let_def)

end
