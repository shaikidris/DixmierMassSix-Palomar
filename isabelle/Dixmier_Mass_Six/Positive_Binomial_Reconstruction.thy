theory Positive_Binomial_Reconstruction
 imports "Positive_Cut_Root_Budget"
   "Positive_One_Root_Factorization"
   "Diagonal_Binomial_Face"
begin

lemma native_weighted_monomial_eq:
 "[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b=biv_monom lam a b"
 for lam::complex
proof -
 have scalar: "[:[:lam:]:]=monom (monom lam 0) 0" by (simp add: monom_0)
 show ?thesis by (simp only: scalar biv_monom_def monom_power mult_monom)
   (simp add: monom_0)
qed

lemma positive_face_eq_of_linear_power_cut:
 fixes P::"complex poly_operator" and lam alpha::complex and sigma a k::nat
 assumes degree: "v_degree 1 (int sigma) P=int(a+sigma*k)"
 and cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
 shows "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
proof -
 let ?X="biv_monom (1::complex) 1 0"
 let ?Y="biv_monom (1::complex) 0 1"
 let ?F="[:[:lam:]:]*?X^a*(?Y-[:[:alpha:]:]*?X^sigma)^k"
 have xhom: "weighted_homogeneous 1 (int sigma) 1 ?X"
   by (simp add: weighted_homogeneous_def weighted_support_monom pair_weight_def)
 have yhom: "weighted_homogeneous 1 (int sigma) (int sigma) ?Y"
   by (simp add: weighted_homogeneous_def weighted_support_monom pair_weight_def)
 have xshom: "weighted_homogeneous 1 (int sigma) (int sigma) (?X^sigma)"
   using cut_homogeneous_power[OF xhom, where k=sigma] by simp
 have binhom: "weighted_homogeneous 1 (int sigma) (int sigma) (?Y-[:[:alpha:]:]*?X^sigma)"
   by (rule cut_homogeneous_diff[OF yhom native_homogeneous_scalar_multiple[OF xshom]])
 have xa: "weighted_homogeneous 1 (int sigma) (int a) (?X^a)"
   using cut_homogeneous_power[OF xhom, where k=a] by simp
 have bk: "weighted_homogeneous 1 (int sigma) (int sigma*int k) ((?Y-[:[:alpha:]:]*?X^sigma)^k)"
   using cut_homogeneous_power[OF binhom, where k=k] by (simp add: mult.commute)
 have shaped: "weighted_homogeneous 1 (int sigma) (int(a+sigma*k)) ?F"
   using cut_homogeneous_mult[OF native_homogeneous_scalar_multiple[OF xa] bk] by simp
 have face_hom: "weighted_homogeneous 1 (int sigma) (int(a+sigma*k)) (leading_form 1 (int sigma) P)"
   unfolding degree[symmetric] leading_form_def by (rule weighted_component_homogeneous)
 have diff: "map_poly (\<lambda>p::complex poly. poly p 1)(A-B)=
   map_poly (\<lambda>p. poly p 1) A-map_poly (\<lambda>p. poly p 1) B" for A B
   by (rule poly_eqI) (simp add: coeff_map_poly poly_diff)
 have multiply: "map_poly (\<lambda>p::complex poly. poly p 1)(A*B)=
   map_poly (\<lambda>p. poly p 1) A*map_poly (\<lambda>p. poly p 1) B" for A B
   using cut_specialize_hom unfolding coefficient_hom_def by blast
 have special: "map_poly (\<lambda>p. poly p 1) ?F=[:lam:]*[:-alpha,1:]^k"
   by (simp only: multiply coefficient_hom_power[OF cut_specialize_hom] diff)
     (simp add: biv_monom_def map_poly_monom poly_monom map_poly_pCons monom_Suc monom_0 one_pCons[symmetric])
 show ?thesis by (rule homogeneous_eq_of_specialization_eq[OF _ face_hom shaped])
   (simp, simp only: cut_poly_def[symmetric] special cut)
qed

lemma preliminary_positive_cut_factorization:
 fixes P Q::"complex poly_operator" and sigma::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q" and sigma: "1<sigma"
 shows "(\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 (int sigma) P=[:lam:]) \<or>
   (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k)"
proof -
 have direction: "is_direction 1 (int sigma)" using sigma by (simp add: is_direction_def)
 have positive: "0<v_degree 1 (int sigma) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have face_nonzero: "leading_form 1 (int sigma) P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree[OF positive])
 have homogeneous: "weighted_homogeneous 1 (int sigma) (v_degree 1 (int sigma) P) (leading_form 1 (int sigma) P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have cutnz: "cut_poly 1 (int sigma) P\<noteq>0"
 proof
   assume zero: "cut_poly 1 (int sigma) P=0"
   have zerohom: "weighted_homogeneous 1 (int sigma) (v_degree 1 (int sigma) P) (0::complex bivariate)"
     by (simp add: weighted_homogeneous_def)
   have special: "map_poly (\<lambda>p. poly p 1) (leading_form 1 (int sigma) P)=map_poly (\<lambda>p. poly p 1) (0::complex bivariate)"
     using zero by (simp add: cut_poly_def)
   have "leading_form 1 (int sigma) P=0"
     by (rule homogeneous_eq_of_specialization_eq[OF zero_less_one homogeneous zerohom special])
   then show False using face_nonzero by contradiction
 qed
 show ?thesis by (rule complex_polynomial_one_root_factorization[OF cutnz preliminary_positive_cut_distinct_roots_le_one[OF source pair sigma]])
qed

lemma positive_cut_degree_axis_exponent:
 fixes P::"complex poly_operator" and sigma::nat
 assumes cutnz: "cut_poly 1 (int sigma) P\<noteq>0"
 shows "\<exists>a::nat. v_degree 1 (int sigma) P=int(a+sigma*degree(cut_poly 1 (int sigma) P))"
proof -
 let ?j="degree(cut_poly 1 (int sigma) P)"
 let ?F="leading_form 1 (int sigma) P"
 have top: "coeff(cut_poly 1 (int sigma) P) ?j\<noteq>0" using cutnz by simp
 have rownz: "coeff ?F ?j\<noteq>0" using top by (auto simp: cut_poly_coeff)
 obtain i::nat where coefficient: "coeff(coeff ?F ?j) i\<noteq>0"
   using rownz by (metis poly_eqI coeff_0)
 have member: "(i,?j)\<in>biv_support ?F" using coefficient by (simp add: biv_support_def biv_coeff_def)
 have weight: "pair_weight 1 (int sigma) (i,?j)=v_degree 1 (int sigma) P"
   using member by (simp add: leading_form_def weighted_component_support)
 have equation: "v_degree 1 (int sigma) P=int(i+sigma*degree(cut_poly 1 (int sigma) P))"
   using weight by (simp only: pair_weight_def fst_conv snd_conv mult_1_right of_nat_add of_nat_mult mult.commute; arith)
 show ?thesis by (rule exI[where x=i], rule equation)
qed

lemma preliminary_positive_face_binomial:
 fixes P Q::"complex poly_operator" and sigma::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
 shows "\<exists>lam alpha::complex. \<exists>a k::nat. lam\<noteq>0 \<and> alpha\<noteq>0 \<and> 1\<le>k \<and>
   v_degree 1 (int sigma) P=int(a+sigma*k) \<and>
   leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
proof -
 have alternatives: "(\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 (int sigma) P=[:lam:]) \<or>
   (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k)"
   by (rule preliminary_positive_cut_factorization[OF source pair sigma])
 from alternatives show ?thesis
 proof
   assume constant_case: "\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 (int sigma) P=[:lam:]"
   then obtain lam where lam: "lam\<noteq>0" and cut: "cut_poly 1 (int sigma) P=[:lam:]" by blast
   have cutnz: "cut_poly 1 (int sigma) P\<noteq>0" using lam by (simp add: cut)
   have exponent_exists: "\<exists>a::nat. v_degree 1 (int sigma) P=int a"
     using positive_cut_degree_axis_exponent[where P=P and sigma=sigma, OF cutnz] by (simp add: cut)
   obtain a::nat where degree: "v_degree 1 (int sigma) P=int a"
     using exponent_exists by blast
   have shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a"
     using positive_face_eq_of_linear_power_cut[where P=P and lam=lam and alpha=0 and sigma=sigma and a=a and k=0] degree cut by simp
   have support: "card(biv_support(leading_form 1 (int sigma) P))\<le>1"
     using native_weighted_monomial_eq[where lam=lam and a=a and b=0] lam
     by (simp add: shape weighted_support_monom)
   show ?thesis using face support by (simp add: in_direction_def)
 next
   assume power_case: "\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
   then obtain lam alpha k where lam: "lam\<noteq>0" and k: "1\<le>k"
     and cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k" by blast
   have cutnz: "cut_poly 1 (int sigma) P\<noteq>0" using lam by (simp add: cut)
   have exponent_exists: "\<exists>a::nat. v_degree 1 (int sigma) P=int(a+sigma*k)"
     using positive_cut_degree_axis_exponent[where P=P and sigma=sigma, OF cutnz]
     by (simp add: cut degree_mult_eq degree_power_eq lam)
   obtain a::nat where degree: "v_degree 1 (int sigma) P=int(a+sigma*k)"
     using exponent_exists by blast
   have shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
     by (rule positive_face_eq_of_linear_power_cut[OF degree cut])
   have alpha: "alpha\<noteq>0"
   proof
     assume az: "alpha=0"
     have reduced: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
       using shape by (simp add: az)
     have monomial: "leading_form 1 (int sigma) P=biv_monom lam a k"
       by (rule trans[OF reduced native_weighted_monomial_eq])
     have support: "card(biv_support(leading_form 1 (int sigma) P))\<le>1"
       by (simp add: monomial weighted_support_monom lam)
     show False using face support by (simp add: in_direction_def)
   qed
   show ?thesis using lam alpha k degree shape by blast
 qed
qed

end
