theory Ramified_Shear_Top_Face
  imports Ramified_Top_Face_Weight
begin
lemma ramified_top_face_polynomial_zero:
  "0<l \<Longrightarrow> ramified_top_face_polynomial l rho sigma 0=0"
  by (simp add: ramified_top_face_polynomial_def ramified_pbw_coeffs_zero)

lemma ramified_weight_deg_upper:
  "p\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
  by (auto simp: ramified_weight_deg_def intro: Max_ge simp: ramified_pbw_support_finite)

lemma ramified_cut_aut_top_face_eq_translate:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    "(i,j)\<in>ramified_pbw_support l T" "ramified_weight l rho sigma (i,j)=rho*r"
    "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>rho*r"
  shows "ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c T)=rho*r \<and>
    ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c T)=
      pcompose (ramified_top_face_polynomial l rho sigma T) [:c,1:]"
proof -
  let ?U = "ramified_cut_aut l rho sigma c T"
  have old: "ramified_weight_deg l rho sigma T=rho*r"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use assms(6,7,8) in blast)+
  have data: "(\<exists>u n. (u,n)\<in>ramified_pbw_support l ?U \<and>
      ramified_weight l rho sigma (u,n)=rho*r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l ?U \<longrightarrow>ramified_weight l rho sigma (u,n)\<le>rho*r)"
    by (rule ramified_cut_aut_preserves_max_weight_data[OF assms(1,2,3,4,5,6,7)])
       (use assms(8) in auto)
  have new: "ramified_weight_deg l rho sigma ?U=rho*r"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use data in auto)+
  have oldface: "ramified_top_face_polynomial l rho sigma T=
    ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)"
    by (rule ramified_top_face_polynomial_eq_cut_face[OF assms(1,2,3,4) old])
       (simp add: old assms(8))
  have newface: "ramified_top_face_polynomial l rho sigma ?U=
    ramified_face_polynomial l ?U r (ramified_cut_exponent l rho sigma)"
    by (rule ramified_top_face_polynomial_eq_cut_face[OF assms(1)
      ramified_cut_aut_mem[OF assms(1,2)] assms(3,4) new]) (use data new in auto)
  have translation: "ramified_face_polynomial l ?U r (ramified_cut_exponent l rho sigma)=
    pcompose (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)) [:c,1:]"
    by (rule ramified_cut_aut_face_eq_translate_of_weight_upper[OF assms(1,2,3,4,5)])
       (use assms(8) in auto)
  show ?thesis by (simp add: new oldface newface translation)
qed

lemma ramified_cut_aut_top_face_eq_translate_of_weight:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    "T\<noteq>0" "ramified_weight_deg l rho sigma T=rho*r"
  shows "ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c T)=rho*r \<and>
    ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c T)=
      pcompose (ramified_top_face_polynomial l rho sigma T) [:c,1:]"
proof -
  obtain A p where p: "p\<in>ramified_pbw_support l T" "ramified_weight l rho sigma p=A"
    and upper: "\<forall>q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q\<le>A"
    using exists_ramified_pbw_support_max_weight[OF
      ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,2,6)], of rho sigma] by blast
  have A: "A=rho*r"
    using ramified_weight_deg_eq_of_attained_upper[of l T rho sigma A] p upper assms(7) by blast
  obtain i j where ij: "p=(i,j)" by (cases p) auto
  show ?thesis by (rule ramified_cut_aut_top_face_eq_translate[OF assms(1,2,3,4,5)])
    (use p ij A upper in auto)
qed
lemma ramified_cut_aut_top_face_translate:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma" "T\<noteq>0"
  shows "ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c T)=
    pcompose (ramified_top_face_polynomial l rho sigma T) [:c,1:]"
proof -
  obtain A p where p: "p\<in>ramified_pbw_support l T" "ramified_weight l rho sigma p=A"
    and upper: "\<forall>q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q\<le>A"
    using exists_ramified_pbw_support_max_weight[OF
      ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,2,6)], of rho sigma] by blast
  obtain i j where ij: "p=(i,j)" by (cases p) auto
  let ?r = "i+ramified_cut_exponent l rho sigma*int j"
  have wt: "ramified_weight l rho sigma (i,j)=rho*?r"
    by (rule ramified_cut_weight_factor[OF assms(4)])
  have A: "A=rho*?r" using p(2) ij wt by simp
  have result: "ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c T)=rho*?r \<and>
    ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c T)=
    pcompose (ramified_top_face_polynomial l rho sigma T) [:c,1:]"
    by (rule ramified_cut_aut_top_face_eq_translate[OF assms(1,2,3,4,5)])
       (use p ij wt upper A in auto)
  show ?thesis using result by blast
qed

lemma ramified_cut_aut_source_companion:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "F\<in>ramified_operator_algebra l"
    "0<rho" "rho dvd int l" "0<rho+sigma" "P\<noteq>0" "F\<noteq>0"
    "ramified_weight_deg l rho sigma P=rho*r"
    "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
    "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
    "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
  shows "ramified_cut_aut l rho sigma c F\<noteq>0 \<and>
    ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c F)=int l*(rho+sigma) \<and>
    ramified_weight_deg l rho sigma (laurent_comp (ramified_cut_aut l rho sigma c P) (ramified_cut_aut l rho sigma c F)-
      laurent_comp (ramified_cut_aut l rho sigma c F) (ramified_cut_aut l rho sigma c P))=
      ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c P) \<and>
    ramified_top_face_polynomial l rho sigma (laurent_comp (ramified_cut_aut l rho sigma c P) (ramified_cut_aut l rho sigma c F)-
      laurent_comp (ramified_cut_aut l rho sigma c F) (ramified_cut_aut l rho sigma c P))=
      ramified_top_face_polynomial l rho sigma (ramified_cut_aut l rho sigma c P)"
proof -
  let ?C = "ramified_cut_aut l rho sigma c"
  let ?H = "laurent_comp P F-laurent_comp F P"
  have carrier: "?H\<in>ramified_operator_algebra l"
    by (intro ramified_algebra_diff ramified_algebra_comp) (rule assms(2) assms(3))+
  have Hne: "?H\<noteq>0"
    using assms(12) ramified_top_face_polynomial_ne_zero[OF assms(1,2,4,7)]
      ramified_top_face_polynomial_zero[OF assms(1), of rho sigma] by auto
  have hom: "ramified_alg_hom_on l ?C"
    by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier assms(1))
  have comm: "?C ?H=laurent_comp (?C P) (?C F)-laurent_comp (?C F) (?C P)"
    by (simp only: ramified_hom_diff[OF hom ramified_algebra_comp[OF assms(2,3)]
      ramified_algebra_comp[OF assms(3,2)]] ramified_hom_comp[OF hom assms(2,3)]
      ramified_hom_comp[OF hom assms(3,2)])
  have Fne: "?C F\<noteq>0"
  proof
    assume zero: "?C F=0"
    have inverse: "ramified_shear_hom l (-ramified_cut_shift l rho sigma c) (?C F)=F"
      using ramified_cut_aut_certificate[OF assms(1), of rho sigma c] assms(3)
      by (auto simp: ramified_alg_aut_on_def)
    have "F=0" using inverse zero
      by (simp add: ramified_shear_hom_def ramified_shear_candidate_zero_operator[OF assms(1)])
    then show False using assms(8) by contradiction
  qed
  have Pw: "ramified_weight_deg l rho sigma (?C P)=ramified_weight_deg l rho sigma P"
    by (rule ramified_cut_aut_weight_deg_eq[OF assms(1,2,4,5,6,7)])
  have Fw: "ramified_weight_deg l rho sigma (?C F)=ramified_weight_deg l rho sigma F"
    by (rule ramified_cut_aut_weight_deg_eq[OF assms(1,3,4,5,6,8)])
  have Hw: "ramified_weight_deg l rho sigma (?C ?H)=ramified_weight_deg l rho sigma ?H"
    by (rule ramified_cut_aut_weight_deg_eq[OF assms(1) carrier assms(4,5,6) Hne])
  have Pf: "ramified_top_face_polynomial l rho sigma (?C P)=
    pcompose (ramified_top_face_polynomial l rho sigma P) [:c,1:]"
    by (rule ramified_cut_aut_top_face_translate[OF assms(1,2,4,5,6,7)])
  have Hf: "ramified_top_face_polynomial l rho sigma (?C ?H)=
    pcompose (ramified_top_face_polynomial l rho sigma ?H) [:c,1:]"
    by (rule ramified_cut_aut_top_face_translate[OF assms(1) carrier assms(4,5,6) Hne])
  show ?thesis by (simp only: comm[symmetric] Fne Fw assms(10,11,12) Pw Hw Pf Hf) simp
qed
end
