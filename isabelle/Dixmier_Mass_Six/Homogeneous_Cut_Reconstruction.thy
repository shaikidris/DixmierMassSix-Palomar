theory Homogeneous_Cut_Reconstruction
 imports "GGV_Case_Field_Adapter"
   "Weighted_Degree_Bounds"
begin

lemma homogeneous_specialization_coeff_at_support:
 fixes F::"complex bivariate"
 assumes rho: "0<rho" and homogeneous: "weighted_homogeneous rho sigma m F"
   and weight: "pair_weight rho sigma (i,j)=m"
 shows "coeff (map_poly (\<lambda>p. poly p 1) F) j=biv_coeff F i j"
proof -
 have row: "coeff F j=monom (biv_coeff F i j) i"
 proof (rule poly_eqI)
   fix k
   show "coeff (coeff F j) k=coeff (monom (biv_coeff F i j) i) k"
   proof (cases "k=i")
     case True then show ?thesis by (simp add: biv_coeff_def)
   next
     case False
     have zero: "biv_coeff F k j=0"
     proof (rule ccontr)
       assume nonzero: "\<not>biv_coeff F k j=0"
       have member: "(k,j)\<in>biv_support F" using nonzero by (simp add: biv_support_def)
       have other: "pair_weight rho sigma (k,j)=m"
         using homogeneous member unfolding weighted_homogeneous_def by blast
       have product: "rho*int k=rho*int i" using weight other by (simp only: pair_weight_def fst_conv snd_conv mult.commute; linarith)
       have "k=i" using product rho by simp
       then show False using False by contradiction
     qed
     show ?thesis using zero False by (simp add: biv_coeff_def)
   qed
 qed
 show ?thesis by (simp add: coeff_map_poly row poly_monom)
qed

lemma homogeneous_eq_of_specialization_eq:
 fixes F G::"complex bivariate"
 assumes rho: "0<rho" and F: "weighted_homogeneous rho sigma m F"
   and G: "weighted_homogeneous rho sigma m G"
   and specialization: "map_poly (\<lambda>p. poly p 1) F=map_poly (\<lambda>p. poly p 1) G"
 shows "F=G"
proof (rule poly_eqI, rule poly_eqI)
 fix j i
 show "coeff (coeff F j) i=coeff (coeff G j) i"
 proof (cases "pair_weight rho sigma (i,j)=m")
   case True
   have Feq: "coeff (map_poly (\<lambda>p. poly p 1) F) j=biv_coeff F i j"
     by (rule homogeneous_specialization_coeff_at_support[OF rho F True])
   have Geq: "coeff (map_poly (\<lambda>p. poly p 1) G) j=biv_coeff G i j"
     by (rule homogeneous_specialization_coeff_at_support[OF rho G True])
   show ?thesis using Feq Geq specialization by (simp add: biv_coeff_def)
 next
   case False
   have zero: "biv_coeff H i j=0" if homogeneous: "weighted_homogeneous rho sigma m H" for H
     using homogeneous False by (auto simp: weighted_homogeneous_def biv_support_def)
   show ?thesis using zero[OF F] zero[OF G] by (simp only: biv_coeff_def)
 qed
qed

lemma diagonal_cut_natDegree_le:
 fixes P::"complex poly_operator"
 assumes degree: "v_degree 1 1 P=int n"
 shows "degree (cut_poly 1 1 P)\<le>n"
proof (rule degree_le, intro allI impI)
 fix j assume above: "n<j"
 have homogeneous: "weighted_homogeneous 1 1 (int n) (leading_form 1 1 P)"
   by (simp only: leading_form_def degree[symmetric]; rule weighted_component_homogeneous)
 have row_zero: "coeff (leading_form 1 1 P) j=0"
 proof (rule poly_eqI)
   fix i
   have impossible: "pair_weight 1 1 (i,j)\<noteq>int n" using above by (simp add: pair_weight_def; arith)
   have zero: "biv_coeff (leading_form 1 1 P) i j=0"
     using homogeneous impossible by (auto simp: weighted_homogeneous_def biv_support_def)
   show "coeff (coeff (leading_form 1 1 P) j) i=coeff 0 i"
     using zero by (simp add: biv_coeff_def)
 qed
 show "coeff (cut_poly 1 1 P) j=0" by (simp add: cut_poly_coeff row_zero)
qed


lemma cut_homogeneous_diff:
 assumes p: "weighted_homogeneous rho sigma m (p::complex bivariate)"
   and q: "weighted_homogeneous rho sigma m q"
 shows "weighted_homogeneous rho sigma m (p-q)"
 using biv_support_diff_subset p q unfolding weighted_homogeneous_def by blast

lemma cut_homogeneous_mult:
 assumes p: "weighted_homogeneous rho sigma m (p::complex bivariate)"
   and q: "weighted_homogeneous rho sigma n q"
 shows "weighted_homogeneous rho sigma (m+n) (p*q)"
 unfolding weighted_homogeneous_def
proof (intro ballI)
 fix u assume member: "u\<in>biv_support(p*q)"
 have pweight: "pair_weight rho sigma v=m" if "v\<in>biv_support p" for v
   using p that unfolding weighted_homogeneous_def by blast
 have qweight: "pair_weight rho sigma v=n" if "v\<in>biv_support q" for v
   using q that unfolding weighted_homogeneous_def by blast
 have upper: "pair_weight rho sigma u\<le>m+n"
   by (rule biv_support_weight_product[OF _ _ member]) (use pweight qweight in auto)
 have opposite: "pair_weight (-rho) (-sigma) v= -pair_weight rho sigma v" for v
   by (simp add: pair_weight_def algebra_simps)
 have lower: "pair_weight (-rho) (-sigma) u\<le> -m+ -n"
   by (rule biv_support_weight_product[OF _ _ member])
      (use pweight qweight in \<open>auto simp: opposite\<close>)
 show "pair_weight rho sigma u=m+n" using upper lower by (simp only: opposite; arith)
qed

lemma cut_homogeneous_power:
 assumes homogeneous: "weighted_homogeneous rho sigma m (p::complex bivariate)"
 shows "weighted_homogeneous rho sigma (int k*m) (p^k)"
proof (induction k)
 case 0
 have support_one: "biv_support(1::complex bivariate)={(0,0)}"
  using weighted_support_monom[where c="1::complex" and a=0 and b=0]
  by (simp add: biv_monom_def monom_0 one_pCons)
 show ?case by (auto simp: weighted_homogeneous_def support_one pair_weight_def)
next
 case (Suc k)
 have product: "weighted_homogeneous rho sigma (m+int k*m) (p*p^k)"
   by (rule cut_homogeneous_mult[OF homogeneous Suc.IH])
 show ?case using product by (simp add: algebra_simps)
qed

lemma cut_diagonal_X_homogeneous:
 "weighted_homogeneous 1 1 1 (biv_monom (1::complex) 1 0)"
 by (simp add: weighted_homogeneous_def weighted_support_monom pair_weight_def)

lemma cut_diagonal_Y_homogeneous:
 "weighted_homogeneous 1 1 1 (biv_monom (1::complex) 0 1)"
 by (simp add: weighted_homogeneous_def weighted_support_monom pair_weight_def)

lemma cut_specialize_hom:
 "coefficient_hom (map_poly (\<lambda>p::complex poly. poly p 1))"
 by (rule coefficient_hom_map_poly[OF coefficient_hom_poly_eval])

lemma diagonal_face_eq_of_factored_cut:
 fixes P::"complex poly_operator" and lam alpha beta::complex
 assumes degree: "v_degree 1 1 P=int(a+u+v)"
   and cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
 shows "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
   (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
proof -
 let ?X="biv_monom (1::complex) 1 0"
 let ?Y="biv_monom (1::complex) 0 1"
 let ?F="[:[:lam:]:]*?X^a*(?Y-[:[:alpha:]:]*?X)^u*(?Y-[:[:beta:]:]*?X)^v"
 have alpha_hom: "weighted_homogeneous 1 1 1 (?Y-[:[:alpha:]:]*?X)"
   by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous
     native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have beta_hom: "weighted_homogeneous 1 1 1 (?Y-[:[:beta:]:]*?X)"
   by (rule cut_homogeneous_diff[OF cut_diagonal_Y_homogeneous
     native_homogeneous_scalar_multiple[OF cut_diagonal_X_homogeneous]])
 have xa: "weighted_homogeneous 1 1 (int a) (?X^a)"
   using cut_homogeneous_power[OF cut_diagonal_X_homogeneous, where k=a] by simp
 have au: "weighted_homogeneous 1 1 (int u) ((?Y-[:[:alpha:]:]*?X)^u)"
   using cut_homogeneous_power[OF alpha_hom, where k=u] by simp
 have bv: "weighted_homogeneous 1 1 (int v) ((?Y-[:[:beta:]:]*?X)^v)"
   using cut_homogeneous_power[OF beta_hom, where k=v] by simp
 have shaped: "weighted_homogeneous 1 1 (int(a+u+v)) ?F"
   using cut_homogeneous_mult[OF cut_homogeneous_mult[OF
     native_homogeneous_scalar_multiple[OF xa] au] bv] by simp
 have face_hom: "weighted_homogeneous 1 1 (int(a+u+v)) (leading_form 1 1 P)"
   unfolding degree[symmetric] leading_form_def by (rule weighted_component_homogeneous)
 have diff: "map_poly (\<lambda>p::complex poly. poly p 1) (A-B)=
   map_poly (\<lambda>p. poly p 1) A-map_poly (\<lambda>p. poly p 1) B" for A B
   by (rule poly_eqI) (simp add: coeff_map_poly poly_diff)
 have multiply: "map_poly (\<lambda>p::complex poly. poly p 1) (A*B)=
   map_poly (\<lambda>p. poly p 1) A*map_poly (\<lambda>p. poly p 1) B" for A B
   using cut_specialize_hom unfolding coefficient_hom_def by blast
 have special: "map_poly (\<lambda>p. poly p 1) ?F=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
   by (simp only: multiply
     coefficient_hom_power[OF cut_specialize_hom] diff)
      (simp add: biv_monom_def map_poly_monom poly_monom map_poly_pCons monom_Suc monom_0 pCons_one)
 show ?thesis by (rule homogeneous_eq_of_specialization_eq[OF _ face_hom shaped])
   (simp, simp only: cut_poly_def[symmetric] special cut)
qed

lemma diagonal_face_eq_of_constant_cut:
 fixes P::"complex poly_operator" and lam::complex
 assumes degree: "v_degree 1 1 P=int n" and cut: "cut_poly 1 1 P=[:lam:]"
 shows "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^n"
 using diagonal_face_eq_of_factored_cut[where P=P and lam=lam and alpha=0 and beta=0
   and a=n and u=0 and v=0] degree cut by simp

lemma counterexample_diagonal_cut_ne_zero:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "cut_poly 1 1 P\<noteq>0"
proof
 assume cut_zero: "cut_poly 1 1 P=0"
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 1 P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have face_nonzero: "leading_form 1 1 P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree[OF positive])
 have homogeneous: "weighted_homogeneous 1 1 (v_degree 1 1 P) (leading_form 1 1 P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have zero_homogeneous: "weighted_homogeneous 1 1 (v_degree 1 1 P) (0::complex bivariate)"
   by (simp add: weighted_homogeneous_def)
 have specialized: "map_poly (\<lambda>p. poly p 1) (leading_form 1 1 P)=
   map_poly (\<lambda>p. poly p 1) (0::complex bivariate)"
   using cut_zero by (simp add: cut_poly_def)
 have "leading_form 1 1 P=0"
   by (rule homogeneous_eq_of_specialization_eq[OF _ homogeneous zero_homogeneous specialized]) simp
 then show False using face_nonzero by contradiction
qed

end
