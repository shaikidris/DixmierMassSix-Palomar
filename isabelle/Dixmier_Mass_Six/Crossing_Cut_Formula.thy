theory Crossing_Cut_Formula
 imports "Crossing_Substitution_Derivatives"
   "Homogeneous_Cut_Reconstruction"
begin

lemma crossing_cut_specialize_add:
 "map_poly (\<lambda>q. poly q 1) (F+G)=map_poly (\<lambda>q. poly q 1) F+map_poly (\<lambda>q. poly q 1) G"
 for F G::"complex bivariate"
 using cut_specialize_hom unfolding coefficient_hom_def by auto

lemma crossing_cut_specialize_mult:
 "map_poly (\<lambda>q. poly q 1) (F*G)=map_poly (\<lambda>q. poly q 1) F*map_poly (\<lambda>q. poly q 1) G"
 for F G::"complex bivariate"
 using cut_specialize_hom unfolding coefficient_hom_def by auto

lemma crossing_cut_specialize_monom:
 "map_poly (\<lambda>q. poly q 1) (biv_monom c a b)=[:c:]*[:0,1:]^b"
 for c::complex
 proof -
 have "map_poly (\<lambda>q. poly q 1) (biv_monom c a b)=
   map_poly (\<lambda>q. poly q 1) (monom (monom c a) b)"
   by (simp only: biv_monom_def)
 also have "...=monom c b"
   by (subst map_poly_monom)
     (simp_all only: poly_0 poly_monom power_one mult_1_right)
 also have "...=[:c:]*[:0,1:]^b" by (simp add: monom_altdef)
 finally show ?thesis .
qed

lemma crossing_substitution_eval:
 fixes p::"complex poly" and s rho::nat
 shows "map_poly (\<lambda>q. poly q 1) (biv_univariate_eval p (biv_monom 1 s rho))=pcompose p ([:0,1:]^rho)"
proof (induction p)
 case 0 then show ?case by simp
next
 case (pCons c p)
 show ?case
  by (simp only: biv_univariate_eval_pCons crossing_cut_specialize_add
   crossing_cut_specialize_mult crossing_cut_specialize_monom pCons.IH
   pcompose_pCons power_0 mult_1_right pCons_one mult_1_left)
qed

lemma crossingFace_general_cutPoly:
 fixes T::"complex poly_operator" and mu::complex and p::"complex poly"
 assumes face: "leading_form(int rho)(-int s) T=[:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval p (biv_monom 1 s rho))^k"
 shows "cut_poly(int rho)(-int s) T=[:mu:]*[:0,1:]^(b*k)*pcompose (p^k) ([:0,1:]^rho)"
proof -
 have scalar: "map_poly (\<lambda>q::complex poly. poly q 1) [:[:mu:]:]=[:mu:]"
   using crossing_cut_specialize_monom[of mu 0 0]
   by (simp only: biv_monom_def monom_0 power_0 mult_1_right)
 have compose_power: "pcompose(p^k) W=(pcompose p W)^k" for W::"complex poly"
   by (induction k) (simp_all add: pcompose_mult pcompose_1)
 show ?thesis
  by (simp only: cut_poly_def face crossing_cut_specialize_mult
   coefficient_hom_power[OF cut_specialize_hom] scalar
   crossing_cut_specialize_monom crossing_substitution_eval pCons_one mult_1_left
   power_mult_distrib power_mult compose_power mult.assoc)
qed

lemma homogeneous_specialization_natDegree_eq_degreeOf_Y:
 fixes F::"complex bivariate"
 assumes rho: "0<rho" and homogeneous: "weighted_homogeneous rho sigma m F"
 shows "degree(map_poly (\<lambda>q. poly q 1) F)=degree F"
proof (cases "F=0")
 case True then show ?thesis by simp
next
 case False
 have row: "coeff F(degree F)\<noteq>0" by (rule leading_coeff_neq_0[OF False])
 obtain i where coefficient: "coeff(coeff F(degree F))i\<noteq>0" using row by (auto simp: poly_eq_iff)
 have member: "(i,degree F)\<in>biv_support F" using coefficient by (simp add: biv_support_def biv_coeff_def)
 have weight: "pair_weight rho sigma(i,degree F)=m" using homogeneous member unfolding weighted_homogeneous_def by blast
 have leading: "coeff(map_poly (\<lambda>q. poly q 1) F)(degree F)\<noteq>0"
  using homogeneous_specialization_coeff_at_support[OF rho homogeneous weight] coefficient by (simp add: biv_coeff_def)
 have lower: "degree F\<le>degree(map_poly (\<lambda>q. poly q 1) F)" by (rule le_degree[OF leading])
 have upper: "degree(map_poly (\<lambda>q. poly q 1) F)\<le>degree F"
 proof (rule degree_le, intro allI impI)
  fix n assume "degree F<n"
  then have "coeff F n=0" by (rule coeff_eq_0)
  then show "coeff(map_poly (\<lambda>q. poly q 1) F)n=0" by (simp add: coeff_map_poly)
 qed
 show ?thesis using lower upper by arith
qed

end
