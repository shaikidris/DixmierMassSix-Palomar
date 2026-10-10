theory Ramified_Cut_Companion_Strict_Grade
 imports Ramified_Companion_Diagonal_Start
   "Ramified_Cut_Root_Endpoint"
begin

lemma ramifiedCutAut_root_start_grade_ne_zero_of_source_leading_bracket:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and positive: "0<rho*r"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and comm: "laurent_comp Q P-laurent_comp P Q=id"
 and member: "(i,j)\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma (i,j)=rho*r"
 and upper: "\<And>u n. (u,n)\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma (u,n)\<le>rho*r"
 and F: "F\<in>ramified_operator_algebra l" and Fnz: "F\<noteq>0"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and degree: "ramified_weight_deg l rho sigma
   (laurent_comp (ramified_cut_aut l rho sigma c P) F-laurent_comp F (ramified_cut_aut l rho sigma c P))=
   ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c P)"
 and face: "ramified_top_face_polynomial l rho sigma
   (laurent_comp (ramified_cut_aut l rho sigma c P) F-laurent_comp F (ramified_cut_aut l rho sigma c P))=
   ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c P)"
 shows "r-ramified_cut_exponent l rho sigma*int(rootMultiplicity c (ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))-
   int l*int(rootMultiplicity c (ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))\<noteq>0"
proof
 let ?k="ramified_cut_exponent l rho sigma"
 let ?m="rootMultiplicity c (ramified_face_polynomial l P r ?k)"
 let ?U="ramified_cut_aut l rho sigma c P"
 assume zero: "r-?k*int ?m-int l*int ?m=0"
 have U: "?U\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have endpoints: "((r-?k*int ?m,?m)\<in>ramified_pbw_support l ?U \<and>
   ramified_weight l rho sigma (r-?k*int ?m,?m)=rho*r) \<and>
   (\<forall>u n. (u,n)\<in>ramified_pbw_support l ?U \<longrightarrow>
     ramified_weight l rho sigma (u,n)=rho*r \<longrightarrow> ?m\<le>n)"
   by (rule ramifiedCutAut_root_start_on_old_face[OF l P rho div sum member top upper])
 have upper_set: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>rho*r"
   using upper by auto
 have Uweight: "ramified_weight_deg l rho sigma ?U=rho*r"
   using ramified_cut_aut_top_face_eq_translate[OF l P rho div sum member top upper_set] by blast
 have Unz: "?U\<noteq>0"
   using endpoints l by (auto simp: ramified_pbw_support_def ramified_pbw_coeffs_zero)
 have diagonal: "r-?k*int ?m=int l*int ?m" using zero by arith
 have m: "0<?m"
 proof (rule ccontr)
   assume "\<not>0<?m"
   then have mzero: "?m=0" by arith
   have rzero: "r=0" using diagonal by (simp only: mzero; simp)
   show False using positive by (simp only: rzero; simp)
 qed
 have point: "(int l*int ?m,?m)\<in>ramified_pbw_support l ?U"
   using endpoints by (simp only: diagonal)
 have point_weight: "ramified_weight l rho sigma (int l*int ?m,?m)=ramified_weight_deg l rho sigma ?U"
   using endpoints by (simp only: diagonal Uweight; blast)
 have minimum: "?m\<le>n" if "n\<in>polynomial_support(ramified_top_face_polynomial l rho sigma ?U)" for n
 proof -
   have data: "n\<in>Poly_Mapping.keys(ramified_pbw_coeffs l ?U) \<and>
     ramified_weight l rho sigma (ramified_pbw_top_laurent l ?U n,n)=rho*r"
     using that by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_weight_def Uweight)
   have atom: "(ramified_pbw_top_laurent l ?U n,n)\<in>ramified_pbw_support l ?U"
     by (rule ramified_pbw_top_laurent_support) (use data in blast)
   show ?thesis using endpoints atom data by blast
 qed
 show False by (rule ramified_no_diagonal_start_of_source_leading_bracket[OF l rho sum U F Unz Fnz
   degree face Fweight m point point_weight minimum])
qed

lemma ramifiedCutAut_maxRoot_grade_negative_of_source_companion:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and positive: "0<rho*r"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and comm: "laurent_comp Q P-laurent_comp P Q=id"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and member: "(i,j)\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma (i,j)=rho*r"
 and upper: "\<And>u n. (u,n)\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma (u,n)\<le>rho*r"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and old_end: "r-(ramified_cut_exponent l rho sigma+int l)*int(degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
 and maximum: "rootMultiplicity c (ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))=
   max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))"
 shows "r-(ramified_cut_exponent l rho sigma+int l)*int(rootMultiplicity c (ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
proof -
 let ?k="ramified_cut_exponent l rho sigma"
 let ?p="ramified_face_polynomial l P r ?k"
 let ?C="ramified_cut_aut l rho sigma c"
 have upper_set: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>rho*r"
 proof (intro ballI)
   fix p assume p: "p\<in>ramified_pbw_support l P"
   obtain u n where coordinates: "p=(u,n)" by (cases p) simp
   show "ramified_weight l rho sigma p\<le>rho*r"
     by (simp only: coordinates; rule upper) (use p in \<open>simp add: coordinates\<close>)
 qed
 have attained: "\<exists>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p=rho*r"
   by (rule bexI[where x="(i,j)"]) (rule top, rule member)
 have Pweight: "ramified_weight_deg l rho sigma P=rho*r"
   by (rule ramified_weight_deg_eq_of_attained_upper[OF attained upper_set])
 have upper_weight: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
   by (simp only: Pweight; rule upper_set)
 have nonpositive: "r-(?k+int l)*int(max_root_mult ?p)\<le>0"
   by (rule ramified_source_companion_cut_grade_nonpositive_of_old_end[OF l rho div sum P F Pnz Fnz
     Pweight upper_weight degree face Fweight Pdegree old_end])
 have transported: "?C F\<noteq>0 \<and> ramified_weight_deg l rho sigma (?C F)=int l*(rho+sigma) \<and>
   ramified_weight_deg l rho sigma (laurent_comp (?C P) (?C F)-laurent_comp (?C F) (?C P))=
     ramified_weight_deg l rho sigma (?C P) \<and>
   ramified_top_face_polynomial l rho sigma (laurent_comp (?C P) (?C F)-laurent_comp (?C F) (?C P))=
     ramified_top_face_polynomial l rho sigma (?C P)"
   by (rule ramified_cut_aut_source_companion[OF l P F rho div sum Pnz Fnz Pweight Fweight degree face])
 have Fpost: "?C F\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l F])
 have Fpostnz: "?C F\<noteq>0" using transported by blast
 have Fpostweight: "ramified_weight_deg l rho sigma (?C F)=int l*(rho+sigma)" using transported by blast
 have Fpostdegree: "ramified_weight_deg l rho sigma (laurent_comp (?C P) (?C F)-laurent_comp (?C F) (?C P))=
   ramified_weight_deg l rho sigma (?C P)" using transported by blast
 have Fpostface: "ramified_top_face_polynomial l rho sigma (laurent_comp (?C P) (?C F)-laurent_comp (?C F) (?C P))=
   ramified_top_face_polynomial l rho sigma (?C P)" using transported by blast
 have nonzero: "r-?k*int(rootMultiplicity c ?p)-int l*int(rootMultiplicity c ?p)\<noteq>0"
   by (rule ramifiedCutAut_root_start_grade_ne_zero_of_source_leading_bracket[OF l rho div sum positive
     P Q comm member top upper Fpost Fpostnz Fpostweight Fpostdegree Fpostface])
 have combined_nonzero: "r-(?k+int l)*int(rootMultiplicity c ?p)\<noteq>0"
   using nonzero by (simp add: algebra_simps)
 have combined_nonpositive: "r-(?k+int l)*int(rootMultiplicity c ?p)\<le>0"
   by (simp only: maximum nonpositive)
 show ?thesis using combined_nonzero combined_nonpositive by arith
qed

lemma ramifiedCutAut_exists_maxRoot_negative_grade_of_source_companion:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and positive: "0<rho*r"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and comm: "laurent_comp Q P-laurent_comp P Q=id"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and member: "(i,j)\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma (i,j)=rho*r"
 and upper: "\<And>u n. (u,n)\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma (u,n)\<le>rho*r"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and old_end: "r-(ramified_cut_exponent l rho sigma+int l)*int(degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
 shows "\<exists>c. poly(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))c=0 \<and>
   rootMultiplicity c (ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))=
     max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)) \<and>
   (r-ramified_cut_exponent l rho sigma*int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))),
     max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))\<in>
     ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<and>
   r-(ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
proof -
 let ?k="ramified_cut_exponent l rho sigma"
 let ?p="ramified_face_polynomial l P r ?k"
 have upper_set: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>rho*r"
 proof (intro ballI)
   fix p assume p: "p\<in>ramified_pbw_support l P"
   obtain u n where coordinates: "p=(u,n)" by (cases p) simp
   show "ramified_weight l rho sigma p\<le>rho*r"
     by (simp only: coordinates; rule upper) (use p in \<open>simp add: coordinates\<close>)
 qed
 have attained: "\<exists>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p=rho*r"
   by (rule bexI[where x="(i,j)"]) (rule top, rule member)
 have Pweight: "ramified_weight_deg l rho sigma P=rho*r"
   by (rule ramified_weight_deg_eq_of_attained_upper[OF attained upper_set])
 have upper_weight: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
   by (simp only: Pweight; rule upper_set)
 have equal: "ramified_top_face_polynomial l rho sigma P=?p"
   by (rule ramified_top_face_polynomial_eq_cut_face[OF l P rho div Pweight upper_weight])
 have pdegree: "0<degree ?p" using Pdegree by (simp only: equal)
 obtain c where root: "poly ?p c=0" and maximum: "rootMultiplicity c ?p=max_root_mult ?p"
   using native_complex_polynomial_max_root_exists[OF pdegree] by blast
 have selected: "(r-?k*int(max_root_mult ?p),max_root_mult ?p)\<in>
   ramified_pbw_support l (ramified_cut_aut l rho sigma c P)"
   using ramifiedCutAut_root_start_on_old_face[OF l P rho div sum member top upper, where c=c]
   by (simp only: maximum; blast)
 have negative: "r-(?k+int l)*int(max_root_mult ?p)<0"
   using ramifiedCutAut_maxRoot_grade_negative_of_source_companion[OF l rho div sum positive P Q F comm Pnz Fnz
     member top upper degree face Fweight Pdegree old_end maximum]
   by (simp only: maximum)
 show ?thesis by (intro exI[of _ c]) (use root maximum selected negative in blast)
qed

end
