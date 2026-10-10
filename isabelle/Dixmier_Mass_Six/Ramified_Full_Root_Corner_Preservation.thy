theory Ramified_Full_Root_Corner_Preservation
  imports Ramified_Cut_Root_Endpoint
begin

lemma ramified_full_degree_root_cut_preserves_canonical_endpoint:
  fixes l :: nat and rho sigma :: int and P :: laurent_operator
  assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l"
    and rho: "0<rho" and divides: "rho dvd int l" and sum: "0<rho+sigma" and Pnz: "P\<noteq>0"
    and full: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=
      degree (ramified_top_face_polynomial l rho sigma P)"
  shows "(ramified_pbw_top_laurent l P (degree (ramified_top_face_polynomial l rho sigma P)),
      degree (ramified_top_face_polynomial l rho sigma P))
      \<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<and>
    ramified_weight l rho sigma
      (ramified_pbw_top_laurent l P (degree (ramified_top_face_polynomial l rho sigma P)),
        degree (ramified_top_face_polynomial l rho sigma P))=ramified_weight_deg l rho sigma P \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<longrightarrow>
      ramified_weight l rho sigma (u,n)=ramified_weight_deg l rho sigma P \<longrightarrow>
      degree (ramified_top_face_polynomial l rho sigma P)\<le>n)"
proof -
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?N = "degree ?f"
  let ?i = "ramified_pbw_top_laurent l P ?N"
  let ?k = "ramified_cut_exponent l rho sigma"
  let ?r = "?i+?k*int ?N"
  have fnz: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
  have support: "?N\<in>polynomial_support ?f" using fnz by (simp add: polynomial_support_def)
  have key: "?N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    and endpoint: "rho*?i+int l*sigma*int ?N=ramified_weight_deg l rho sigma P"
    using support by (simp_all only: ramified_top_face_polynomial_mem_support_iff)
  have member: "(?i,?N)\<in>ramified_pbw_support l P"
    by (rule ramified_pbw_top_laurent_support[OF key])
  have endpoint_weight: "ramified_weight l rho sigma (?i,?N)=ramified_weight_deg l rho sigma P"
    using endpoint by (simp add: ramified_weight_def)
  have factor: "ramified_weight l rho sigma (?i,?N)=rho*?r"
    by (rule ramified_cut_weight_factor[OF divides])
  have degree_weight: "ramified_weight_deg l rho sigma P=rho*?r"
    using endpoint_weight factor by simp
  have upper: "\<forall>p\<in>ramified_pbw_support l P.
    ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
    using ramified_weight_deg_upper by blast
  have faces: "?f=ramified_face_polynomial l P ?r ?k"
    by (rule ramified_top_face_polynomial_eq_cut_face[OF l P rho divides degree_weight upper])
  have multiplicity: "rootMultiplicity c (ramified_face_polynomial l P ?r ?k)=?N"
    using full by (simp only: faces[symmetric])
  have bounded: "\<And>u n. (u,n)\<in>ramified_pbw_support l P \<Longrightarrow>
    ramified_weight l rho sigma (u,n)\<le>rho*?r"
  proof -
    fix u n assume member: "(u,n)\<in>ramified_pbw_support l P"
    have "ramified_weight l rho sigma (u,n)\<le>ramified_weight_deg l rho sigma P"
      by (rule ramified_weight_deg_upper[OF member])
    then show "ramified_weight l rho sigma (u,n)\<le>rho*?r" by (simp only: degree_weight)
  qed
  have start: "((?r-?k*int ?N,?N)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<and>
      ramified_weight l rho sigma (?r-?k*int ?N,?N)=rho*?r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<longrightarrow>
      ramified_weight l rho sigma (u,n)=rho*?r \<longrightarrow> ?N\<le>n)"
  proof -
    have root_start: "((?r-?k*int(rootMultiplicity c (ramified_face_polynomial l P ?r ?k)),
        rootMultiplicity c (ramified_face_polynomial l P ?r ?k))\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<and>
      ramified_weight l rho sigma (?r-?k*int(rootMultiplicity c (ramified_face_polynomial l P ?r ?k)),
        rootMultiplicity c (ramified_face_polynomial l P ?r ?k))=rho*?r) \<and>
      (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P) \<longrightarrow>
        ramified_weight l rho sigma (u,n)=rho*?r \<longrightarrow>rootMultiplicity c (ramified_face_polynomial l P ?r ?k)\<le>n)"
      by (rule ramifiedCutAut_root_start_on_old_face[where r="?r" and c=c,
        OF l P rho divides sum member factor]) (rule bounded)
    show ?thesis using root_start by (auto simp: multiplicity)
  qed
  have index: "?r-?k*int ?N=?i" by simp
  show ?thesis using start endpoint_weight by (auto simp: index degree_weight[symmetric])
qed

end
