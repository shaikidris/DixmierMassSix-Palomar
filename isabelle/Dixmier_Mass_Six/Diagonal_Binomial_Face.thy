theory Diagonal_Binomial_Face
 imports "Homogeneous_Cut_Reconstruction"
   "Fourier_Diagonal_Endpoints"
   "Sparse_Power_Divisibility"
begin

lemma binomial_specialized_variable:
 "(monom 1 (Suc 0)::complex poly)=[:0,1:]"
 by (simp only: monom_Suc monom_0)

lemma binomial_specialized_linear:
 "(monom 1 (Suc 0)::complex poly)-[:alpha:]=[:-alpha,1:]"
 by (simp add: binomial_specialized_variable)

lemma binomial_support_nonempty:
 fixes F::"complex bivariate"
 assumes F: "F\<noteq>0"
 shows "biv_support F\<noteq>{}"
proof
 assume empty: "biv_support F={}"
 have "F=0"
  by (rule biv_eqI) (use empty in \<open>auto simp: biv_support_def\<close>)
 then show False using F by contradiction
qed

lemma cutPoly_termCount_le_mass:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and sum: "0<rho+sigma"
 shows "termCount(cut_poly rho sigma P)\<le>weyl_mass P"
proof -
 let ?F="leading_form rho sigma P"
 have subset: "sparse_support(cut_poly rho sigma P)\<subseteq>snd ` biv_support ?F"
 proof (intro subsetI)
   fix j assume j: "j\<in>sparse_support(cut_poly rho sigma P)"
   have nonzero: "poly (coeff ?F j) 1\<noteq>0" using j
     by (simp add: sparse_support_def cut_poly_coeff)
   have row: "coeff ?F j\<noteq>0"
   proof
     assume "coeff ?F j=0"
     then have "poly (coeff ?F j) 1=0" by simp
     then show False using nonzero by contradiction
   qed
   have exists: "\<exists>i. coeff(coeff ?F j) i\<noteq>0"
   proof (rule ccontr)
     assume "\<not>(\<exists>i. coeff(coeff ?F j) i\<noteq>0)"
     then have "coeff ?F j=0" by (intro poly_eqI) auto
     then show False using row by contradiction
   qed
   obtain i where coefficient: "coeff(coeff ?F j) i\<noteq>0" using exists by blast
   have member: "(i,j)\<in>biv_support ?F" using coefficient by (simp add: biv_support_def biv_coeff_def)
   show "j\<in>snd ` biv_support ?F" using imageI[OF member, where f=snd] by simp
 qed
 have bound: "termCount(cut_poly rho sigma P)\<le>card(snd ` biv_support ?F)"
   unfolding termCount_def by (rule card_mono) (simp, rule subset)
 have image_bound: "card(snd ` biv_support ?F)\<le>card(biv_support ?F)" by (rule card_image_le) simp
 show ?thesis by (rule order_trans[OF order_trans[OF bound image_bound] face_term_count_le_mass[OF P sum]])
qed

lemma positive_binomial_face_cut:
 fixes P::"complex poly_operator" and lam alpha::complex and sigma a k::nat
 assumes shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
 shows "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
proof -
 have diff: "map_poly (\<lambda>p::complex poly. poly p 1) (A-B)=
   map_poly (\<lambda>p. poly p 1) A-map_poly (\<lambda>p. poly p 1) B" for A B
   by (rule poly_eqI) (simp add: coeff_map_poly poly_diff)
 have mult: "map_poly (\<lambda>p::complex poly. poly p 1) (A*B)=
   map_poly (\<lambda>p. poly p 1) A*map_poly (\<lambda>p. poly p 1) B" for A B
   using cut_specialize_hom unfolding coefficient_hom_def by blast
 show ?thesis unfolding cut_poly_def shape
   by (simp only: mult coefficient_hom_power[OF cut_specialize_hom] diff)
     (simp add: biv_monom_def map_poly_monom poly_monom map_poly_pCons binomial_specialized_variable diff_pCons)
qed

lemma positive_binomial_top_face_point:
 fixes P::"complex poly_operator" and lam alpha::complex and sigma a k::nat
 assumes lam: "lam\<noteq>0" and weight: "v_degree 1 (int sigma) P=int(a+sigma*k)"
   and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
 shows "(a,k)\<in>biv_support(leading_form 1 (int sigma) P) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 (int sigma) P). snd e\<le>k)"
proof -
 let ?F="leading_form 1 (int sigma) P"
 have cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
   by (rule positive_binomial_face_cut[OF shape])
 have degree: "degree(cut_poly 1 (int sigma) P)=k"
   by (simp add: cut degree_mult_eq degree_power_eq lam)
 have nz: "cut_poly 1 (int sigma) P\<noteq>0" using lam by (simp add: cut)
 have top: "coeff(cut_poly 1 (int sigma) P) k\<noteq>0"
   using leading_coeff_neq_0[OF nz] by (simp only: degree; blast)
 have homogeneous: "weighted_homogeneous 1 (int sigma) (int(a+sigma*k)) ?F"
   unfolding weight[symmetric] leading_form_def by (rule weighted_component_homogeneous)
 have w: "pair_weight 1 (int sigma) (a,k)=int(a+sigma*k)" by (simp add: pair_weight_def)
 have coefficient: "coeff(cut_poly 1 (int sigma) P) k=biv_coeff ?F a k"
   unfolding cut_poly_def by (rule homogeneous_specialization_coeff_at_support[OF zero_less_one homogeneous w])
 have member: "(a,k)\<in>biv_support ?F" using top coefficient by (simp add: biv_support_def)
 have bounded: "snd e\<le>k" if "e\<in>biv_support ?F" for e
 proof -
   have w: "pair_weight 1 (int sigma) e=int(a+sigma*k)"
     using homogeneous that unfolding weighted_homogeneous_def by blast
   have eq: "coeff(cut_poly 1 (int sigma) P) (snd e)=biv_coeff ?F (fst e) (snd e)"
     unfolding cut_poly_def by (rule homogeneous_specialization_coeff_at_support[OF zero_less_one homogeneous]) (use w in simp)
   have nonzero: "coeff(cut_poly 1 (int sigma) P) (snd e)\<noteq>0" using eq that by (simp add: biv_support_def)
   show ?thesis using le_degree[OF nonzero] by (simp only: degree)
 qed
 show ?thesis using member bounded by blast
qed

lemma diagonal_x_factor_vDeg:
 fixes P::"complex poly_operator" and a k::nat and lam alpha::complex
 assumes lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "v_degree 1 1 P=int(a+k)"
proof -
 let ?X="biv_monom (1::complex) 1 0"
 let ?Y="biv_monom (1::complex) 0 1"
 have binomial: "weighted_homogeneous 1 1 1 (?Y-[:[:alpha:]:]*?X)"
   by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous
     native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have Xpower: "weighted_homogeneous 1 1 (int a) (?X^a)"
   using cut_homogeneous_power[OF cut_diagonal_X_homogeneous, where k=a] by simp
 have Bpower: "weighted_homogeneous 1 1 (int k) ((?Y-[:[:alpha:]:]*?X)^k)"
   using cut_homogeneous_power[OF binomial, where k=k] by simp
 have shaped: "weighted_homogeneous 1 1 (int(a+k)) (leading_form 1 1 P)"
   using cut_homogeneous_mult[OF native_homogeneous_scalar_multiple[OF Xpower] Bpower]
   by (simp only: shape; simp)
 have cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k"
   using positive_binomial_face_cut[where P=P and sigma=1 and a=a and k=k and lam=lam and alpha=alpha] shape by simp
 have nonzero: "leading_form 1 1 P\<noteq>0"
 proof
   assume "leading_form 1 1 P=0"
   then have "cut_poly 1 1 P=0" by (simp add: cut_poly_def)
   then show False using cut lam by simp
 qed
 obtain e where e: "e\<in>biv_support(leading_form 1 1 P)" using binomial_support_nonempty[OF nonzero] by blast
 have actual: "pair_weight 1 1 e=v_degree 1 1 P"
   using e by (simp add: leading_form_def weighted_component_support)
 have prescribed: "pair_weight 1 1 e=int(a+k)"
   using shaped e unfolding weighted_homogeneous_def by blast
 show ?thesis using actual prescribed by arith
qed

lemma diagonal_binomial_total_degree_of_weight:
 fixes P::"complex poly_operator" and n::nat
 assumes weight: "v_degree 1 1 P=int n" and face: "leading_form 1 1 P\<noteq>0"
 shows "total_degree P=n"
proof -
 obtain e where e: "e\<in>biv_support(leading_form 1 1 P)" using binomial_support_nonempty[OF face] by blast
 have total: "fst e+snd e=total_degree P" by (rule diagonal_face_point_total_degree[OF e])
 have actual: "pair_weight 1 1 e=int n" using e weight
   by (simp add: leading_form_def weighted_component_support)
 show ?thesis using actual total by (simp add: pair_weight_def)
qed

lemma diagonal_x_factor_mass_ge_ten:
 fixes P Q::"complex poly_operator" and a k::nat and lam alpha::complex
 assumes bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and less: "a<k" and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "10\<le>weyl_mass P"
proof -
 have weight: "v_degree 1 1 P=int(a+k)" by (rule diagonal_x_factor_vDeg[OF lam shape])
 have cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k"
   using positive_binomial_face_cut[where P=P and sigma=1 and a=a and k=k and lam=lam and alpha=alpha] shape by simp
 have nz: "cut_poly 1 1 P\<noteq>0" using lam by (simp add: cut)
 have face: "leading_form 1 1 P\<noteq>0" using nz by (auto simp: cut_poly_def)
 have degree: "total_degree P=a+k" by (rule diagonal_binomial_total_degree_of_weight[OF weight face])
 have large: "16\<le>a+k" using bound[OF pair] degree by simp
 have divides: "([:0,1:]-[:alpha:])^k dvd cut_poly 1 1 P"
   by (rule dvdI[where k="[:lam:]"]) (simp add: cut mult.commute)
 have terms: "k<termCount(cut_poly 1 1 P)" by (rule pow_dvd_imp_lt_termCount[OF nz alpha divides])
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have mass: "termCount(cut_poly 1 1 P)\<le>weyl_mass P"
   by (rule cutPoly_termCount_le_mass[OF P]) simp
 show ?thesis using less large terms mass by arith
qed


lemma diagonal_y_factor_cut:
 fixes P::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "cut_poly 1 1 P=[:lam:]*[:0,1:]^b*[:-alpha,1:]^k"
proof -
 have diff: "map_poly (\<lambda>p::complex poly. poly p 1) (A-B)=
   map_poly (\<lambda>p. poly p 1) A-map_poly (\<lambda>p. poly p 1) B" for A B
   by (rule poly_eqI) (simp add: coeff_map_poly poly_diff)
 have mult: "map_poly (\<lambda>p::complex poly. poly p 1) (A*B)=
   map_poly (\<lambda>p. poly p 1) A*map_poly (\<lambda>p. poly p 1) B" for A B
   using cut_specialize_hom unfolding coefficient_hom_def by blast
 show ?thesis unfolding cut_poly_def shape
   by (simp only: mult coefficient_hom_power[OF cut_specialize_hom] diff)
     (simp add: biv_monom_def map_poly_monom poly_monom map_poly_pCons binomial_specialized_variable diff_pCons)
qed

lemma diagonal_y_factor_vDeg:
 fixes P::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "v_degree 1 1 P=int(b+k)"
proof -
 let ?X="biv_monom (1::complex) 1 0"
 let ?Y="biv_monom (1::complex) 0 1"
 have binomial: "weighted_homogeneous 1 1 1 (?Y-[:[:alpha:]:]*?X)"
   by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous
     native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have Ypower: "weighted_homogeneous 1 1 (int b) (?Y^b)"
   using cut_homogeneous_power[OF cut_diagonal_Y_homogeneous, where k=b] by simp
 have Bpower: "weighted_homogeneous 1 1 (int k) ((?Y-[:[:alpha:]:]*?X)^k)"
   using cut_homogeneous_power[OF binomial, where k=k] by simp
 have shaped: "weighted_homogeneous 1 1 (int(b+k)) (leading_form 1 1 P)"
   using cut_homogeneous_mult[OF native_homogeneous_scalar_multiple[OF Ypower] Bpower]
   by (simp only: shape; simp)
 have cut: "cut_poly 1 1 P=[:lam:]*[:0,1:]^b*[:-alpha,1:]^k"
   by (rule diagonal_y_factor_cut[OF shape])
 have nonzero: "leading_form 1 1 P\<noteq>0"
 proof
   assume "leading_form 1 1 P=0"
   then have "cut_poly 1 1 P=0" by (simp add: cut_poly_def)
   then show False using cut lam by simp
 qed
 obtain e where e: "e\<in>biv_support(leading_form 1 1 P)" using binomial_support_nonempty[OF nonzero] by blast
 have actual: "pair_weight 1 1 e=v_degree 1 1 P"
   using e by (simp add: leading_form_def weighted_component_support)
 have prescribed: "pair_weight 1 1 e=int(b+k)"
   using shaped e unfolding weighted_homogeneous_def by blast
 show ?thesis using actual prescribed by arith
qed

lemma diagonal_y_factor_totalDeg:
 fixes P::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes k: "1\<le>k" and lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "total_degree P=b+k"
proof -
 have weight: "v_degree 1 1 P=int(b+k)" by (rule diagonal_y_factor_vDeg[OF lam shape])
 have cut: "cut_poly 1 1 P=[:lam:]*[:0,1:]^b*[:-alpha,1:]^k"
   by (rule diagonal_y_factor_cut[OF shape])
 have nz: "cut_poly 1 1 P\<noteq>0" using lam by (simp add: cut)
 have face: "leading_form 1 1 P\<noteq>0" using nz by (auto simp: cut_poly_def)
 show ?thesis by (rule diagonal_binomial_total_degree_of_weight[OF weight face])
qed

lemma diagonal_y_factor_mass_ge_ten:
 fixes P Q::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and less: "b<k" and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "10\<le>weyl_mass P"
proof -
 have k: "1\<le>k" using less by arith
 have degree: "total_degree P=b+k" by (rule diagonal_y_factor_totalDeg[OF k lam shape])
 have large: "16\<le>b+k" using bound[OF pair] degree by simp
 have cut: "cut_poly 1 1 P=[:lam:]*[:0,1:]^b*[:-alpha,1:]^k"
   by (rule diagonal_y_factor_cut[OF shape])
 have nz: "cut_poly 1 1 P\<noteq>0" using lam by (simp add: cut)
 have divides: "([:0,1:]-[:alpha:])^k dvd cut_poly 1 1 P"
   by (rule dvdI[where k="[:lam:]*[:0,1:]^b"])
     (simp add: cut mult.assoc mult.commute mult.left_commute)
 have terms: "k<termCount(cut_poly 1 1 P)" by (rule pow_dvd_imp_lt_termCount[OF nz alpha divides])
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have mass: "termCount(cut_poly 1 1 P)\<le>weyl_mass P"
   by (rule cutPoly_termCount_le_mass[OF P]) simp
 show ?thesis using less large terms mass by arith
qed

lemma binomial_X_power_monom:
 "([:0,1:]::complex poly)^b=monom 1 b"
 using monom_altdef[where c="1::complex" and n=b] by simp

lemma diagonal_y_factor_first_face_point:
 fixes P::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "(k,b)\<in>biv_support(leading_form 1 1 P) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 1 P). fst e\<le>k)"
proof -
 let ?F="leading_form 1 1 P"
 have weight: "v_degree 1 1 P=int(b+k)" by (rule diagonal_y_factor_vDeg[OF lam shape])
 have hom: "weighted_homogeneous 1 1 (int(b+k)) ?F"
   unfolding weight[symmetric] leading_form_def by (rule weighted_component_homogeneous)
 have cut: "cut_poly 1 1 P=[:0,1:]^b*([:lam:]*[:-alpha,1:]^k)"
   using diagonal_y_factor_cut[OF shape] by (simp only: mult.assoc mult.commute mult.left_commute)
 have coefficient: "coeff(cut_poly 1 1 P) b\<noteq>0"
   using lam alpha by (simp add: cut binomial_X_power_monom coeff_monom_mult poly_0_coeff_0[symmetric])
 have w: "pair_weight 1 1 (k,b)=int(b+k)" by (simp add: pair_weight_def)
 have coefficient_eq: "coeff(cut_poly 1 1 P) b=biv_coeff ?F k b"
   unfolding cut_poly_def by (rule homogeneous_specialization_coeff_at_support[OF zero_less_one hom w])
 have member: "(k,b)\<in>biv_support ?F" using coefficient coefficient_eq by (simp add: biv_support_def)
 have bound: "fst e\<le>k" if e: "e\<in>biv_support ?F" for e
 proof -
   have ew: "pair_weight 1 1 e=int(b+k)" using hom e unfolding weighted_homogeneous_def by blast
   have ce: "coeff(cut_poly 1 1 P) (snd e)=biv_coeff ?F (fst e) (snd e)"
     unfolding cut_poly_def by (rule homogeneous_specialization_coeff_at_support[OF zero_less_one hom]) (use ew in simp)
   have nonzero: "coeff(cut_poly 1 1 P) (snd e)\<noteq>0" using e ce by (simp add: biv_support_def)
   have low: "b\<le>snd e"
   proof (rule ccontr)
     assume "\<not>b\<le>snd e"
     then have below: "snd e<b" by arith
     have zero: "coeff(cut_poly 1 1 P) (snd e)=0"
       by (simp add: cut binomial_X_power_monom coeff_monom_mult below)
     show False using nonzero zero by contradiction
   qed
   show ?thesis using low ew by (simp add: pair_weight_def; arith)
 qed
 show ?thesis using member bound by blast
qed

end
