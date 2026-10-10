theory Ramified_Corner_Endpoint_Geometry
  imports "Ramified_Shear_Top_Face"
begin

lemma ramified_face_weight_grade_identity:
  "r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))-
    (int l*(r+s))*(int(snd E)-int(snd p))=
    ramified_weight l r s p-ramified_weight l r s E"
  by (simp add: ramified_weight_def algebra_simps)

lemma ramified_face_grade_min_of_order_max:
  assumes l: "0<l" and r: "0<r" and sum: "0<r+s"
    and face: "ramified_weight l r s p=ramified_weight l r s E" and order: "snd p\<le>snd E"
  shows "fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
proof -
  have factor: "0<int l*(r+s)" using l sum by (intro mult_pos_pos) auto
  have delta: "0\<le>int(snd E)-int(snd p)" using order by simp
  have nonnegative: "0\<le>(int l*(r+s))*(int(snd E)-int(snd p))"
    by (rule mult_nonneg_nonneg) (use factor delta in auto)
  have identity: "r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))=
    (int l*(r+s))*(int(snd E)-int(snd p))"
    using ramified_face_weight_grade_identity[of r p l E s] face by arith
  have "0\<le>r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))"
    using identity nonnegative by simp
  then have "0\<le>(fst p-int l*int(snd p))-(fst E-int l*int(snd E))" using r by (auto simp only: zero_le_mult_iff; arith)
  then show ?thesis by arith
qed

lemma ramified_strict_lower_face_order_le_preserved_point:
  assumes l: "0<l" and r: "0<r" and strict: "rho*s<r*sigma"
    and old: "ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
    and tie: "ramified_weight l r s p=ramified_weight l r s E"
  shows "snd p\<le>snd E"
proof -
  have algebra: "r*(ramified_weight l rho sigma p-ramified_weight l rho sigma E)-
    int l*(r*sigma-rho*s)*(int(snd p)-int(snd E))=
    rho*(ramified_weight l r s p-ramified_weight l r s E)"
    by (simp add: ramified_weight_def algebra_simps)
  have identity: "r*(ramified_weight l rho sigma p-ramified_weight l rho sigma E)=
    int l*(r*sigma-rho*s)*(int(snd p)-int(snd E))" using algebra tie by simp
  have factor: "0<int l*(r*sigma-rho*s)" using l strict by (intro mult_pos_pos) auto
  have product: "r*(ramified_weight l rho sigma p-ramified_weight l rho sigma E)\<le>0"
    using r old by (intro mult_nonneg_nonpos) auto
  have inequality: "int l*(r*sigma-rho*s)*(int(snd p)-int(snd E))\<le>0" using identity product by simp
  have cancellation: "int l*(r*sigma-rho*s)*(int(snd p)-int(snd E))\<le>0 \<longleftrightarrow>
    int(snd p)-int(snd E)\<le>0"
    using mult_le_cancel_left_pos[OF factor, of "int(snd p)-int(snd E)" 0] by simp
  have "int(snd p)-int(snd E)\<le>0" using inequality cancellation by blast
  then show ?thesis by simp
qed

lemma ramified_strict_lower_face_preserved_point_min_grade:
  assumes l: "0<l" and r: "0<r" and sum: "0<r+s" and strict: "rho*s<r*sigma"
    and old: "ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
    and tie: "ramified_weight l r s p=ramified_weight l r s E"
  shows "fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
  by (rule ramified_face_grade_min_of_order_max[OF l r sum tie])
    (rule ramified_strict_lower_face_order_le_preserved_point[OF l r strict old tie])

lemma ramified_min_grade_top_canonical_ending:
  fixes T::laurent_operator
  assumes l: "0<l" and carrier: "T\<in>ramified_operator_algebra l"
    and rho: "0<rho" and sum: "0<rho+sigma"
    and E: "E\<in>ramified_pbw_support l T"
    and top: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma T"
    and minimum: "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow>
      ramified_weight l rho sigma p=ramified_weight_deg l rho sigma T \<Longrightarrow>
      fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
  shows "degree (ramified_top_face_polynomial l rho sigma T)=snd E \<and>
    ramified_pbw_top_laurent l T (snd E)=fst E"
proof -
  have upper: "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
    using ramified_weight_deg_upper by blast
  have endpoint: "snd E\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    ramified_pbw_top_laurent l T (snd E)=fst E \<and>
    ramified_weight l rho sigma (ramified_pbw_top_laurent l T (snd E),snd E)=ramified_weight_deg l rho sigma T"
    by (rule ramified_face_point_top_laurent_at_order[OF rho E top upper])
  have maximal: "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T \<longrightarrow> j\<le>snd E"
  proof (intro ballI impI)
    fix j assume j: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
      and weight: "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T"
    let ?p = "(ramified_pbw_top_laurent l T j,j)"
    have p: "?p\<in>ramified_pbw_support l T" by (rule ramified_pbw_top_laurent_support[OF j])
    have pw: "ramified_weight l rho sigma ?p=ramified_weight_deg l rho sigma T" using weight by (simp add: ramified_weight_def)
    have min: "fst E-int l*int(snd E)\<le>fst ?p-int l*int(snd ?p)" by (rule minimum[OF p pw])
    have identity: "rho*((fst ?p-int l*int(snd ?p))-(fst E-int l*int(snd E)))=
      (int l*(rho+sigma))*(int(snd E)-int(snd ?p))"
      using ramified_face_weight_grade_identity[of rho ?p l E sigma] pw top by arith
    have nonnegative: "0\<le>rho*((fst ?p-int l*int(snd ?p))-(fst E-int l*int(snd E)))"
      using rho min by (intro mult_nonneg_nonneg) auto
    have factor: "0<int l*(rho+sigma)" using l sum by (intro mult_pos_pos) auto
    have "0\<le>(int l*(rho+sigma))*(int(snd E)-int j)" using identity nonnegative by simp
    then have "0\<le>int(snd E)-int j" using factor by (auto simp only: zero_le_mult_iff; arith)
    then show "j\<le>snd E" by simp
  qed
  have degree: "degree (ramified_top_face_polynomial l rho sigma T)=snd E"
    by (rule ramified_top_face_polynomial_nat_degree_of_endpoint)
      (use endpoint maximal in \<open>auto simp: ramified_weight_def\<close>)
  show ?thesis using degree endpoint by blast
qed

lemma ramified_strict_lower_face_canonical_degree_at_preserved_point:
  fixes T::laurent_operator
  assumes l: "0<l" and carrier: "T\<in>ramified_operator_algebra l" and r: "0<r"
    and strict: "rho*s<r*sigma" and E: "E\<in>ramified_pbw_support l T"
    and top: "ramified_weight l r s E=ramified_weight_deg l r s T"
    and old: "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
  shows "degree (ramified_top_face_polynomial l r s T)=snd E \<and>
    ramified_pbw_top_laurent l T (snd E)=fst E"
proof -
  have upper: "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l r s p\<le>ramified_weight_deg l r s T"
    using ramified_weight_deg_upper by blast
  have endpoint: "snd E\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    ramified_pbw_top_laurent l T (snd E)=fst E \<and>
    ramified_weight l r s (ramified_pbw_top_laurent l T (snd E),snd E)=ramified_weight_deg l r s T"
    by (rule ramified_face_point_top_laurent_at_order[OF r E top upper])
  have maximal: "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    r*ramified_pbw_top_laurent l T j+int l*s*int j=ramified_weight_deg l r s T \<longrightarrow> j\<le>snd E"
  proof (intro ballI impI)
    fix j assume j: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
      and weight: "r*ramified_pbw_top_laurent l T j+int l*s*int j=ramified_weight_deg l r s T"
    let ?p = "(ramified_pbw_top_laurent l T j,j)"
    have p: "?p\<in>ramified_pbw_support l T" by (rule ramified_pbw_top_laurent_support[OF j])
    have tie: "ramified_weight l r s ?p=ramified_weight l r s E" using weight top by (simp add: ramified_weight_def)
    have "snd ?p\<le>snd E" by (rule ramified_strict_lower_face_order_le_preserved_point[OF l r strict old[OF p] tie])
    then show "j\<le>snd E" by simp
  qed
  have degree: "degree (ramified_top_face_polynomial l r s T)=snd E"
    by (rule ramified_top_face_polynomial_nat_degree_of_endpoint)
      (use endpoint maximal in \<open>auto simp: ramified_weight_def\<close>)
  show ?thesis using degree endpoint by blast
qed

lemma ramified_normalized_corner_new_face_weight_ratio:
  fixes P Q::laurent_operator
  assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and ptop: "ramified_weight l r s (int d*(int l*int h-1),d*h)=ramified_weight_deg l r s P"
    and qtop: "ramified_weight l r s (int n*(int l*int h-1),n*h)=ramified_weight_deg l r s Q"
  shows "ramified_weight_deg l r s Q*int d=ramified_weight_deg l r s P*int n"
  by (simp only: ptop[symmetric] qtop[symmetric]) (simp add: ramified_weight_def algebra_simps)

lemma ramified_normalized_corner_proportion_mate_coordinates:
  assumes d: "0<d" and x: "int n*iP=int d*iQ" and y: "n*jP=d*jQ"
    and corner_x: "iP=int d*(int l*int h-1)" and corner_y: "jP=d*h"
  shows "iQ=int n*(int l*int h-1) \<and> jQ=n*h"
proof -
  have cancel_x: "int d*iQ=int d*(int n*(int l*int h-1))" using x by (auto simp: corner_x mult_ac)
  have dx: "int d\<noteq>0" using d by simp
  have coordinate_x: "iQ=int n*(int l*int h-1)" using cancel_x dx by simp
  have cancel_y: "d*jQ=d*(n*h)" using y by (auto simp: corner_y mult_ac)
  have coordinate_y: "jQ=n*h" using cancel_y d by simp
  show ?thesis using coordinate_x coordinate_y by blast
qed

lemma ramified_normalized_corner_pair_geometry:
  fixes E F::"int\<times>nat"
  assumes d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h"
    and E: "E=(int d*(int l*int h-1),d*h)"
    and F: "F=(int n*(int l*int h-1),n*h)"
  shows "fst E-int l*int(snd E)<0 \<and> fst F-int l*int(snd F)<0 \<and>
    2\<le>snd E \<and> 2\<le>snd F \<and> int(snd E)*fst F=int(snd F)*fst E"
proof -
  have eg: "fst E-int l*int(snd E)= -int d" by (simp add: E algebra_simps)
  have fg: "fst F-int l*int(snd F)= -int n" by (simp add: F algebra_simps)
  have dh: "2\<le>d*h"
  proof -
    have "d\<le>d*h" using h mult_left_mono[of 1 h d] by simp
    then show ?thesis using d by arith
  qed
  have nh: "2\<le>n*h"
  proof -
    have "n\<le>n*h" using h mult_left_mono[of 1 h n] by simp
    then show ?thesis using n by arith
  qed
  have parallel: "int(snd E)*fst F=int(snd F)*fst E" by (simp add: E F algebra_simps)
  show ?thesis using eg fg d n dh nh parallel by (simp add: E F)
qed

end
