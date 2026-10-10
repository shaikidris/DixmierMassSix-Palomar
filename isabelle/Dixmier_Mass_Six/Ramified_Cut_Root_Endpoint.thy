theory Ramified_Cut_Root_Endpoint
  imports Ramified_Canonical_End_Proportion
begin

lemma translated_root_least_coefficient:
  fixes p :: "complex poly"
  assumes pnz: "p\<noteq>0"
  shows "coeff (pcompose p [:c,1:]) (rootMultiplicity c p)\<noteq>0 \<and>
    (\<forall>n. coeff (pcompose p [:c,1:]) n\<noteq>0 \<longrightarrow> rootMultiplicity c p\<le>n)"
proof -
  let ?m = "Polynomial.order c p"
  obtain h where factor: "p=[:-c,1:]^?m*h" and residual: "\<not>[:-c,1:] dvd h"
    using order_decomp[OF pnz, of c] by blast
  have hvalue: "poly h c\<noteq>0" using residual by (auto simp only: poly_eq_0_iff_dvd)
  have linear: "pcompose [:-c,1:] [:c,1:]=[:0,1:]"
    by (simp add: pcompose_pCons algebra_simps)
  have unit_power: "[:0,1:]^?m=monom (1::complex) ?m"
    by (simp add: monom_altdef)
  have composed: "pcompose p [:c,1:]=pcompose ([:-c,1:]^?m*h) [:c,1:]"
    by (rule arg_cong[OF factor])
  have translated: "pcompose p [:c,1:]=monom 1 ?m*pcompose h [:c,1:]"
    using composed by (simp only: pcompose_mult pcompose_power linear unit_power)
  have hzero: "coeff (pcompose h [:c,1:]) 0\<noteq>0"
  proof -
    have "poly (pcompose h [:c,1:]) 0=poly h c" by (simp add: poly_pcompose)
    then show ?thesis using hvalue by (simp add: poly_0_coeff_0)
  qed
  have occupied: "coeff (pcompose p [:c,1:]) ?m\<noteq>0"
    using hzero by (simp add: translated coeff_monom_mult)
  have lower: "\<And>n. coeff (pcompose p [:c,1:]) n\<noteq>0 \<Longrightarrow> ?m\<le>n"
    by (auto simp: translated coeff_monom_mult split: if_splits)
  show ?thesis using occupied lower by (auto simp only: rootMultiplicity_eq_order[OF pnz])
qed

lemma ramifiedCutAut_root_start_on_old_face:
  fixes l j :: nat and rho sigma r i :: int and T :: laurent_operator
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and rho: "0<rho" and divides: "rho dvd int l" and sum: "0<rho+sigma"
    and member: "(i,j)\<in>ramified_pbw_support l T"
    and top: "ramified_weight l rho sigma (i,j)=rho*r"
    and upper: "\<And>u n. (u,n)\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma (u,n)\<le>rho*r"
  shows "((r-ramified_cut_exponent l rho sigma*int(rootMultiplicity c
      (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma))),
      rootMultiplicity c (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)))
      \<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<and>
    ramified_weight l rho sigma
      (r-ramified_cut_exponent l rho sigma*int(rootMultiplicity c
        (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma))),
        rootMultiplicity c (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)))=rho*r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<longrightarrow>
      ramified_weight l rho sigma (u,n)=rho*r \<longrightarrow>
      rootMultiplicity c (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma))\<le>n)"
proof -
  let ?k = "ramified_cut_exponent l rho sigma"
  let ?p = "ramified_face_polynomial l T r ?k"
  let ?U = "ramified_cut_aut l rho sigma c T"
  let ?q = "ramified_face_polynomial l ?U r ?k"
  let ?m = "rootMultiplicity c ?p"
  have pnz: "?p\<noteq>0" by (rule ramified_face_polynomial_ne_zero_of_weight_point[OF l T rho divides member top])
  have translation: "?q=pcompose ?p [:c,1:]"
    by (rule ramified_cut_aut_face_eq_translate_of_weight_upper[OF l T rho divides sum]) (rule upper)
  have least: "coeff ?q ?m\<noteq>0 \<and> (\<forall>n. coeff ?q n\<noteq>0 \<longrightarrow> ?m\<le>n)"
    using translated_root_least_coefficient[OF pnz, where c=c] by (auto simp only: translation)
  have U: "?U\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l T])
  have selected: "(r-?k*int ?m,?m)\<in>ramified_pbw_support l ?U"
    using least by (auto simp only: ramified_pbw_support_mem_iff[OF l U] ramified_face_polynomial_coeff)
  have selected_weight: "ramified_weight l rho sigma (r-?k*int ?m,?m)=rho*r"
    by (simp add: ramified_weight_def algebra_simps ramified_cut_exponent_weight[OF divides])
  have minimum: "\<forall>u n. (u,n)\<in>ramified_pbw_support l ?U \<longrightarrow>
    ramified_weight l rho sigma (u,n)=rho*r \<longrightarrow> ?m\<le>n"
  proof (intro allI impI)
    fix u n assume point: "(u,n)\<in>ramified_pbw_support l ?U"
      and weight: "ramified_weight l rho sigma (u,n)=rho*r"
    have index: "u=r-?k*int n" by (rule ramified_cut_weight_point_index[OF rho divides weight])
    have occupied: "coeff ?q n\<noteq>0"
      using point by (auto simp only: ramified_face_polynomial_coeff index[symmetric] ramified_pbw_support_mem_iff[OF l U])
    show "?m\<le>n" using least occupied by blast
  qed
  show ?thesis using selected selected_weight minimum by blast
qed

lemma ramifiedCutAut_root_start_max_grade:
  fixes l j n :: nat and rho sigma r i u :: int and T :: laurent_operator
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and rho: "0<rho" and divides: "rho dvd int l" and sum: "0<rho+sigma"
    and member: "(i,j)\<in>ramified_pbw_support l T"
    and top: "ramified_weight l rho sigma (i,j)=rho*r"
    and upper: "\<And>v k. (v,k)\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma (v,k)\<le>rho*r"
    and point: "(u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T)"
    and weight: "ramified_weight l rho sigma (u,n)=rho*r"
  shows "u-int l*int n\<le>
    (r-ramified_cut_exponent l rho sigma*int(rootMultiplicity c
      (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma))))-
    int l*int(rootMultiplicity c (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)))"
proof -
  let ?m = "rootMultiplicity c (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma))"
  let ?E = "(r-ramified_cut_exponent l rho sigma*int ?m,?m)"
  have start: "(?E\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<and>
      ramified_weight l rho sigma ?E=rho*r) \<and>
    (\<forall>v k. (v,k)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<longrightarrow>
      ramified_weight l rho sigma (v,k)=rho*r \<longrightarrow> ?m\<le>k)"
    by (rule ramifiedCutAut_root_start_on_old_face[where c=c, OF l T rho divides sum member top]) (rule upper)
  have order: "?m\<le>n" using start point weight by blast
  have tie: "ramified_weight l rho sigma ?E=ramified_weight l rho sigma (u,n)"
    using start weight by auto
  have "fst(u,n)-int l*int(snd(u,n))\<le>fst ?E-int l*int(snd ?E)"
    by (rule ramified_face_grade_min_of_order_max[OF l rho sum tie]) (use order in simp)
  then show ?thesis by simp
qed

end
