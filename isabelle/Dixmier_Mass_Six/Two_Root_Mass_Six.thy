theory Two_Root_Mass_Six
 imports "GGV_Inputs"
   "Diagonal_Binomial_Face"
   "Degree_Minimal_Nondivisibility"
begin

lemma twoRoot_cutPoly:
 fixes T::"complex poly_operator" and lam alpha beta::complex
 assumes face: "leading_form 1 1 T=[:[:lam:]:]*(biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
 (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
 shows "cut_poly 1 1 T=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
proof -
 have mult: "map_poly (\<lambda>p::complex poly. poly p 1)(F*G)=map_poly (\<lambda>p. poly p 1)F*map_poly (\<lambda>p. poly p 1)G" for F G
  using cut_specialize_hom unfolding coefficient_hom_def by blast
 have diff: "map_poly (\<lambda>p::complex poly. poly p 1)(F-G)=map_poly (\<lambda>p. poly p 1)F-map_poly (\<lambda>p. poly p 1)G" for F G
  by (rule poly_eqI) (simp add: coeff_map_poly poly_diff)
 have power: "map_poly (\<lambda>p::complex poly. poly p 1)(F^n)=(map_poly (\<lambda>p. poly p 1)F)^n" for F n
  by (rule coefficient_hom_power[OF cut_specialize_hom])
 have scalar: "map_poly (\<lambda>p::complex poly. poly p 1)[:[:c:]:]=[:c:]" for c
  by (simp add: map_poly_pCons)
 have X: "map_poly (\<lambda>p::complex poly. poly p 1)(biv_monom 1 1 0)=1"
  by (simp add: biv_monom_def map_poly_monom map_poly_pCons poly_monom monom_0 one_pCons)
 have Y: "map_poly (\<lambda>p::complex poly. poly p 1)(biv_monom 1 0 1)=[:0,1:]"
  by (simp add: biv_monom_def map_poly_monom map_poly_pCons poly_monom monom_altdef one_pCons)
 have linear: "map_poly (\<lambda>p::complex poly. poly p 1)(biv_monom 1 0 1-[:[:c:]:]*biv_monom 1 1 0)=[:-c,1:]" for c
  by (simp only: diff mult scalar X Y mult_1_right; simp)
 show ?thesis by (simp only: cut_poly_def face mult power scalar linear)
qed

lemma twoRoot_cutPoly_termCount_gt_exponents:
 fixes T::"complex poly_operator" and lam alpha beta::complex
 assumes lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and beta: "beta\<noteq>0"
 and face: "leading_form 1 1 T=[:[:lam:]:]*(biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
 (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
 shows "u<termCount(cut_poly 1 1 T) \<and> v<termCount(cut_poly 1 1 T)"
proof -
 have shape: "cut_poly 1 1 T=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v" by (rule twoRoot_cutPoly[OF face])
 have nonzero: "cut_poly 1 1 T\<noteq>0" using lam by (simp add: shape)
 have da: "([:0,1:]-[:alpha:])^u dvd cut_poly 1 1 T"
  by (rule dvdI[where k="[:lam:]*[:-beta,1:]^v"]) (simp add: shape mult_ac)
 have db: "([:0,1:]-[:beta:])^v dvd cut_poly 1 1 T"
  by (rule dvdI[where k="[:lam:]*[:-alpha,1:]^u"]) (simp add: shape mult_ac)
 show ?thesis using pow_dvd_imp_lt_termCount[OF nonzero alpha da] pow_dvd_imp_lt_termCount[OF nonzero beta db] by blast
qed

lemma twoRoot_vDeg_eq_exponent_sum:
 fixes T::"complex poly_operator" and lam alpha beta::complex
 assumes lam: "lam\<noteq>0"
 and face: "leading_form 1 1 T=[:[:lam:]:]*(biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
 (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
 shows "v_degree 1 1 T=int(u+v)"
proof -
 let ?F="leading_form 1 1 T"
 let ?A="biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0::complex bivariate"
 let ?B="biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0::complex bivariate"
 have A: "weighted_homogeneous 1 1 1 ?A"
  by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have B: "weighted_homogeneous 1 1 1 ?B"
  by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have Apow: "weighted_homogeneous 1 1 (int u) (?A^u)" using cut_homogeneous_power[OF A, where k=u] by simp
 have Bpow: "weighted_homogeneous 1 1 (int v) (?B^v)" using cut_homogeneous_power[OF B, where k=v] by simp
 have shape_hom: "weighted_homogeneous 1 1 (int(u+v)) ?F"
  using native_homogeneous_scalar_multiple[OF cut_homogeneous_mult[OF Apow Bpow], where c=lam]
  by (simp only: face of_nat_add mult.assoc)
 have face_hom: "weighted_homogeneous 1 1 (v_degree 1 1 T) ?F"
  unfolding leading_form_def by (rule weighted_component_homogeneous)
 have cut_nonzero: "cut_poly 1 1 T\<noteq>0" using twoRoot_cutPoly[OF face] lam by simp
 have F: "?F\<noteq>0" using cut_nonzero by (auto simp: cut_poly_def)
 have nonempty: "biv_support ?F\<noteq>{}" using F
  by (simp only: biv_support_empty_iff not_False_eq_True)
 obtain e::"nat\<times>nat" where e: "e\<in>biv_support ?F" using nonempty by blast
 have ew: "pair_weight 1 1 e=v_degree 1 1 T"
  by (rule bspec[OF face_hom[unfolded weighted_homogeneous_def] e])
 have sw: "pair_weight 1 1 e=int(u+v)"
  by (rule bspec[OF shape_hom[unfolded weighted_homogeneous_def] e])
 show ?thesis by (rule trans[OF sym[OF ew] sw])
qed

lemma twoRoot_totalDeg_eq_exponent_sum:
 fixes T::"complex poly_operator" and lam alpha beta::complex
 assumes T: "T\<in>weyl_algebra" and lam: "lam\<noteq>0" and u: "1\<le>u" and v: "1\<le>v"
 and face: "leading_form 1 1 T=[:[:lam:]:]*(biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
 (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
 shows "total_degree T=u+v"
proof -
 have weight: "v_degree 1 1 T=int(u+v)" by (rule twoRoot_vDeg_eq_exponent_sum[OF lam face])
 have positive: "0<v_degree 1 1 T" using weight u v by simp
 have nonzero: "leading_form 1 1 T\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF positive])
 have nonempty: "biv_support(leading_form 1 1 T)\<noteq>{}" using nonzero
  by (simp only: biv_support_empty_iff not_False_eq_True)
 obtain e::"nat\<times>nat" where e: "e\<in>biv_support(leading_form 1 1 T)" using nonempty by blast
 have total: "fst e+snd e=total_degree T" by (rule diagonal_face_point_total_degree[OF e])
 have ew: "pair_weight 1 1 e=v_degree 1 1 T" using e by (simp add: leading_form_def weighted_component_support)
 have sumcast: "int(fst e+snd e)=int(u+v)" using ew weight by (simp add: pair_weight_def)
 have totalcast: "int(total_degree T)=int(u+v)" using sumcast by (simp only: total)
 show ?thesis by (rule of_nat_eq_iff[where 'a=int, THEN iffD1, OF totalcast])
qed


lemma twoRoot_massSix_contradiction_of_GGV:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
   and mass: "weyl_mass P\<le>6" and two: "two_root_total_symbol P"
 shows False
proof -
 obtain lam alpha beta u v where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and beta: "beta\<noteq>0"
 and u: "1\<le>u" and v: "1\<le>v"
 and shape: "leading_form 1 1 P=biv_monom lam 0 0*(biv_monom 1 0 1-biv_monom alpha 1 0)^u*(biv_monom 1 0 1-biv_monom beta 1 0)^v"
 using two unfolding two_root_total_symbol_def by blast
 have face: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*(biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
  using shape by (simp add: biv_mult_monom biv_monom_def monom_0 smult_monom)
 have P: "P\<in>weyl_algebra" using pair unfolding is_counterexample_pair_def by blast
 have degree: "total_degree P=u+v" by (rule twoRoot_totalDeg_eq_exponent_sum[OF P lam u v face])
 have terms: "u<termCount(cut_poly 1 1 P) \<and> v<termCount(cut_poly 1 1 P)"
  by (rule twoRoot_cutPoly_termCount_gt_exponents[OF lam alpha beta face])
 have cutmass: "termCount(cut_poly 1 1 P)\<le>weyl_mass P"
  by (rule cutPoly_termCount_le_mass[OF P]) simp
 have bound: "15<gcd(total_degree P)(total_degree Q)"
  using inputs pair unfolding GGVInputs_def GGVDegreeBoundInput_def by blast
 have positive: "0<total_degree P" using degree u v by arith
 have gcd_bound: "gcd(total_degree P)(total_degree Q)\<le>total_degree P"
  by (rule gcd_le1_nat) (use positive in arith)
 show False using bound gcd_bound degree terms cutmass mass by arith
qed

end
