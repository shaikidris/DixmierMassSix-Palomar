theory Ramified_Top_Face_Weight
  imports Ramified_Top_Face_Polynomial
begin
lemma ramified_face_point_top_laurent_at_order:
  assumes "0<rho" "B\<in>ramified_pbw_support l T"
    "ramified_weight l rho sigma B=ramified_weight_deg l rho sigma T"
    "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
  shows "snd B\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    ramified_pbw_top_laurent l T (snd B)=fst B \<and>
    ramified_weight l rho sigma (ramified_pbw_top_laurent l T (snd B),snd B)=ramified_weight_deg l rho sigma T"
proof -
  have key: "snd B\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    and atom: "fst B\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) (snd B))"
    using assms(2) by (auto simp: ramified_pbw_support_def)
  have low: "fst B\<le>ramified_pbw_top_laurent l T (snd B)"
    using laurent_top_exponent_upper[OF atom] by (simp add: ramified_pbw_top_laurent_def)
  have top: "(ramified_pbw_top_laurent l T (snd B),snd B)\<in>ramified_pbw_support l T"
    by (rule ramified_pbw_top_laurent_support[OF key])
  have "rho*ramified_pbw_top_laurent l T (snd B)\<le>rho*fst B"
    using assms(3,4) top by (auto simp: ramified_weight_def)
  then have eq: "ramified_pbw_top_laurent l T (snd B)=fst B"
    using low assms(1) by simp
  show ?thesis using key eq assms(3) by simp
qed

lemma ramified_top_face_polynomial_eq_cut_face:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l"
    "ramified_weight_deg l rho sigma T=rho*r"
    "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
  shows "ramified_top_face_polynomial l rho sigma T=
    ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)"
proof (rule poly_eqI)
  fix j
  let ?k = "ramified_cut_exponent l rho sigma"
  show "coeff (ramified_top_face_polynomial l rho sigma T) j =
    coeff (ramified_face_polynomial l T r ?k) j"
  proof (cases "j\<in>polynomial_support (ramified_top_face_polynomial l rho sigma T)")
    case True
    then have top: "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T"
      by (simp add: ramified_top_face_polynomial_mem_support_iff)
    have weight: "ramified_weight l rho sigma (ramified_pbw_top_laurent l T j,j)=rho*r"
      using top assms(5) by (simp add: ramified_weight_def)
    have index: "ramified_pbw_top_laurent l T j=r-?k*int j"
      by (rule ramified_cut_weight_point_index[OF assms(3,4) weight])
    show ?thesis using ramified_top_face_polynomial_coeff_of_mem_support[OF True] index
      by (simp add: ramified_face_polynomial_coeff)
  next
    case False
    then have zero: "coeff (ramified_top_face_polynomial l rho sigma T) j=0"
      by (simp add: polynomial_support_def)
    have facezero: "ramified_pbw_coeff l T (r-?k*int j) j=0"
    proof (rule ccontr)
      assume nonzero: "ramified_pbw_coeff l T (r-?k*int j) j\<noteq>0"
      have atom: "(r-?k*int j,j)\<in>ramified_pbw_support l T"
        using nonzero by (simp add: ramified_pbw_support_mem_iff[OF assms(1,2)])
      have weight: "ramified_weight l rho sigma (r-?k*int j,j)=ramified_weight_deg l rho sigma T"
        using ramified_cut_weight_factor[OF assms(4), where i="r-?k*int j" and j=j and sigma=sigma] assms(5)
        by simp
      have lifted: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
        ramified_weight l rho sigma (ramified_pbw_top_laurent l T j,j)=ramified_weight_deg l rho sigma T"
        using ramified_face_point_top_laurent_at_order[OF assms(3) atom weight assms(6)] by auto
      then have "j\<in>polynomial_support (ramified_top_face_polynomial l rho sigma T)"
        by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_weight_def)
      then show False using False by contradiction
    qed
    show ?thesis by (simp add: zero facezero ramified_face_polynomial_coeff)
  qed
qed

lemma ramified_cut_aut_weight_deg_eq:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l"
    "0<rho+sigma" "P\<noteq>0"
  shows "ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c P)=ramified_weight_deg l rho sigma P"
proof -
  obtain A p where p: "p\<in>ramified_pbw_support l P" "ramified_weight l rho sigma p=A"
    and upper: "\<forall>q\<in>ramified_pbw_support l P. ramified_weight l rho sigma q\<le>A"
    using exists_ramified_pbw_support_max_weight[OF
      ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,2,6)], of rho sigma] by blast
  obtain i j where ij: "p=(i,j)" by (cases p) auto
  let ?r = "i+ramified_cut_exponent l rho sigma*int j"
  have wt: "ramified_weight l rho sigma (i,j)=rho*?r"
    by (rule ramified_cut_weight_factor[OF assms(4)])
  have A: "A=rho*?r" using p(2) ij wt by simp
  have data: "(\<exists>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<and>
      ramified_weight l rho sigma (u,n)=rho*?r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*?r)"
    by (rule ramified_cut_aut_preserves_max_weight_data[OF assms(1,2,3,4,5)])
       (use p ij wt upper A in auto)
  have old: "ramified_weight_deg l rho sigma P=A"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use p upper in blast)+
  have new: "ramified_weight_deg l rho sigma (ramified_cut_aut l rho sigma c P)=rho*?r"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use data in auto)+
  show ?thesis by (simp add: old new A)
qed
end
