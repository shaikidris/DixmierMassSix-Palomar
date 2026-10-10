theory Positive_Companion_Axis
 imports "Companion_Nonmonomial"
   "Face_Mass_Geometry"
   "Poisson_Fixed_Point_Weight"
begin

text \<open>Exact first three producers of GGVPositiveCompanionEndpoint.lean,
source 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Complex bivariate support
pairs represent the source two-variable exponents.\<close>

lemma positive_companion_support_restrict:
 fixes rho sigma::nat and F::"complex bivariate" and e::"nat\<times>nat"
 assumes rho: "0<rho" and slope: "rho<sigma"
   and hom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and occupied: "e\<in>biv_support F"
 shows "snd e=0 \<or> e=(1,1)"
proof -
 have weight: "int rho*int(fst e)+int sigma*int(snd e)=int rho+int sigma"
   using hom occupied by (simp add: weighted_homogeneous_def pair_weight_def mult.commute)
 have rp: "0<(int rho)" using rho by simp
 have sp: "0<(int sigma)" using rho slope by simp
 have rs: "int rho<int sigma" using slope by simp
 show ?thesis
 proof (cases "snd e=0")
   case True then show ?thesis by blast
 next
   case False
   have y: "1\<le>snd e" using False by arith
   have y_eq: "snd e=1"
   proof (rule ccontr)
     assume "snd e\<noteq>1"
     then have two: "2\<le>int(snd e)" using y by arith
     have lower: "2*int sigma\<le>int sigma*int(snd e)"
       using mult_left_mono[OF two, of "int sigma"] sp by simp
     have nonnegative: "0\<le>int rho*int(fst e)" using rp by simp
     show False using weight lower nonnegative rs by linarith
   qed
   have xe: "int rho*int(fst e)=int rho" using weight y_eq by simp
   have x_eq: "fst e=1" using xe rp by simp
   show ?thesis using x_eq y_eq by (simp add: prod_eq_iff)
 qed
qed

lemma positive_companion_has_axis_term:
 fixes rho sigma::nat and R F::"complex bivariate" and m::int
 assumes rho: "0<rho" and slope: "rho<sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)" and companion: "biv_poisson R F=R"
 shows "\<exists>e\<in>biv_support F. snd e=0"
proof (rule ccontr)
 assume absent: "\<not>(\<exists>e\<in>biv_support F. snd e=0)"
 have unique: "e=(1,1)" if "e\<in>biv_support F" for e
   using positive_companion_support_restrict[OF rho slope Fhom that] absent that by blast
 let ?c="biv_coeff F 1 1"
 have mono: "F=biv_monom ?c 1 1"
 proof (rule biv_eqI)
   fix i j
   show "biv_coeff F i j=biv_coeff(biv_monom ?c 1 1) i j"
   proof (cases "(i,j)=(1,1)")
     case True then show ?thesis by simp
   next
     case False
     have "(i,j)\<notin>biv_support F" using unique False by blast
     then show ?thesis using False by (auto simp: biv_support_def)
   qed
 qed
 have scaled: "F=smult [:?c:] (biv_monom 1 1 1)"
   using mono by (simp only: endpoint_biv_smult_monom mult_1_right)
 have action: "biv_poisson R F=smult [:?c:] (biv_poisson R (biv_monom 1 1 1))"
   proof -
  have rewrite: "biv_poisson R F=biv_poisson R (smult [:?c:] (biv_monom 1 1 1))"
   by (rule arg_cong[OF scaled, where f="\<lambda>S. biv_poisson R S"])
  show ?thesis by (rule trans[OF rewrite corner_poisson_smult_right])
 qed
 have coefficient: "?c*(of_nat(snd e)- of_nat(fst e))=1"
   if e: "e\<in>biv_support R" for e
 proof -
   have nz: "biv_coeff R (fst e)(snd e)\<noteq>0" using e by (simp add: biv_support_def)
   have equation: "(?c*(of_nat(snd e)- of_nat(fst e)))*biv_coeff R (fst e)(snd e)=
     1*biv_coeff R (fst e)(snd e)"
     using arg_cong[OF companion, of "\<lambda>p. biv_coeff p (fst e)(snd e)"]
     by (simp only: action biv_coeff_smult poisson_xy_coeff[of R e] mult.assoc mult_1_left)
   show ?thesis using equation nz by simp
 qed
 have nonempty: "biv_support R\<noteq>{}" using face by auto
 obtain d where d: "d\<in>biv_support R" using nonempty by blast
 have c: "?c\<noteq>0" using coefficient[OF d] by auto
 have same: "a=b" if a: "a\<in>biv_support R" and b: "b\<in>biv_support R" for a b
 proof -
   have eq: "(of_nat(snd a)::complex)- of_nat(fst a)=of_nat(snd b)- of_nat(fst b)"
     using coefficient[OF a] coefficient[OF b] c by (metis mult_left_cancel)
   have cast: "(of_int(int(snd a)-int(fst a))::complex)=of_int(int(snd b)-int(fst b))"
     using eq by simp
   have grade: "pair_grade a=pair_grade b" using cast
     by (simp only: of_int_eq_iff pair_grade_def; arith)
   have weight: "pair_weight (int rho) (int sigma) a=pair_weight (int rho) (int sigma) b"
     using Rhom a b by (simp add: weighted_homogeneous_def)
   have sum: "int rho+int sigma\<noteq>0" using rho slope by simp
   show ?thesis by (rule exponent_eq_of_grade_and_weight[OF sum grade weight])
 qed
 have small: "card(biv_support R)\<le>Suc 0"
   by (rule iffD2[OF card_le_Suc0_iff_eq[where A="biv_support R", OF finite_biv_support]])
      (use same in blast)
 show False using small face by arith
qed

lemma positive_companion_first_weight_one:
 fixes rho sigma::nat and R F::"complex bivariate" and m::int
 assumes rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)" and companion: "biv_poisson R F=R"
 shows "rho=1 \<and> (\<exists>e\<in>biv_support F. snd e=0)"
proof -
 obtain e where e: "e\<in>biv_support F" and axis: "snd e=0"
   using positive_companion_has_axis_term[OF rho slope Rhom Fhom face companion] by blast
 have at_e: "pair_weight (int rho) (int sigma) e=int rho+int sigma"
   using Fhom e unfolding weighted_homogeneous_def by blast
 have weight: "int rho*int(fst e)=int rho+int sigma"
   using at_e axis by (simp add: pair_weight_def mult.commute)
 have nat_weight: "rho*fst e=rho+sigma" using weight by (simp only: of_nat_mult[symmetric] of_nat_add[symmetric] of_nat_eq_iff)
 have divides: "rho dvd sigma"
 proof -
   have divisor: "rho dvd rho*fst e" by (rule dvd_triv_left)
   have "rho dvd rho+sigma" using divisor by (simp only: nat_weight)
   then show ?thesis by simp
 qed
 have "rho=1" by (rule coprime_common_divisor_nat[OF primitive dvd_refl divides])
 then show ?thesis using e axis by blast
qed

lemma positive_companion_root_has_axis_term_of_shape:
 fixes sigma::nat and R::"complex bivariate" and c d::complex
 assumes c: "c\<noteq>0" and R: "R\<noteq>0"
   and companion: "biv_poisson R (biv_monom c (sigma+1) 0+smult [:d:] (biv_monom 1 1 1))=R"
 shows "\<exists>e\<in>biv_support R. snd e=0"
proof (rule ccontr)
 assume absent: "\<not>(\<exists>e\<in>biv_support R. snd e=0)"
 have finite: "finite(snd ` biv_support R)" by simp
 have nonempty: "snd ` biv_support R\<noteq>{}" using R by (simp add: biv_support_empty_iff)
 have attained: "Min(snd ` biv_support R)\<in>snd ` biv_support R"
   by (rule Min_in[OF finite nonempty])
 obtain e where image_eq: "Min(snd ` biv_support R)=snd e" and e: "e\<in>biv_support R"
   using attained by (rule imageE)
 have minimum: "snd e=Min(snd ` biv_support R)" by (rule sym[OF image_eq])
 have bound: "snd e\<le>snd a" if "a\<in>biv_support R" for a
   using Min_le[OF finite imageI[OF that, of snd]] by (simp only: minimum)
 have ep: "0<snd e" using absent e by auto
 let ?i="fst e+sigma"
 let ?j="snd e-1"
 have zero: "biv_coeff R ?i ?j=0"
 proof (rule ccontr)
   assume "biv_coeff R ?i ?j\<noteq>0"
   then have "(?i,?j)\<in>biv_support R" by (simp add: biv_support_def)
   then have at_lower: "snd e\<le>snd(?i,?j)" by (rule bound)
   then have "snd e\<le>snd e-1" by simp
   then show False using ep by arith
 qed
 have add_right: "biv_poisson R (A+B)=biv_poisson R A+biv_poisson R B"
   for A B::"complex bivariate"
 proof -
  have dx_add: "biv_dx(A+B)=biv_dx A+biv_dx B"
   unfolding biv_dx_def by (rule poly_eqI) (simp add: coeff_map_poly pderiv_add)
  have dy_add: "biv_dy(A+B)=biv_dy A+biv_dy B" by (simp add: biv_dy_def pderiv_add)
  show ?thesis by (simp only: biv_poisson_def dx_add dy_add; algebra)
 qed
 have axis_action: "biv_poisson R (biv_monom c (sigma+1) 0)=
   biv_monom (of_nat(sigma+1)*c) sigma 0*biv_dy R"
   by (simp add: biv_poisson_def biv_dx_monom biv_dy_monom mult.commute)
 have axis_coeff: "biv_coeff (biv_poisson R (biv_monom c (sigma+1) 0)) ?i ?j=
   of_nat(sigma+1)*c* of_nat(snd e)*biv_coeff R (fst e)(snd e)"
   using ep by (simp only: axis_action biv_coeff_monom_left_mult biv_dy_coeff; simp add: algebra_simps)
 have xy_coeff: "biv_coeff (biv_poisson R (smult [:d:] (biv_monom 1 1 1))) ?i ?j=0"
   by (simp only: corner_poisson_smult_right biv_coeff_smult
     poisson_xy_coeff[of R "(?i,?j)", simplified fst_conv snd_conv] zero mult_zero_right)
 have equation: "of_nat(sigma+1)*c* of_nat(snd e)*biv_coeff R (fst e)(snd e)=0"
   using arg_cong[OF companion, of "\<lambda>p. biv_coeff p ?i ?j"]
   by (simp only: add_right biv_coeff_add axis_coeff xy_coeff zero add_0_right)
 have nz: "biv_coeff R (fst e)(snd e)\<noteq>0" using e by (simp add: biv_support_def)
 have cast_nz: "(of_nat(sigma+1)::complex)\<noteq>0"
   by (simp only: of_nat_eq_0_iff; simp)
 have second_nz: "(of_nat(snd e)::complex)\<noteq>0" using ep
   by (simp only: of_nat_eq_0_iff; arith)
 show False using equation cast_nz c second_nz nz by (simp only: mult_eq_0_iff; blast)
qed

lemma positive_companion_root_has_total_degree_endpoint:
 fixes rho sigma::nat and R F::"complex bivariate" and m::int
 assumes rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)" and companion: "biv_poisson R F=R"
 shows "rho=1 \<and> (nat m,0)\<in>biv_support R \<and>
   (\<forall>e\<in>biv_support R. fst e+snd e\<le>nat m) \<and>
   (\<forall>e\<in>biv_support R. fst e+snd e=nat m \<longrightarrow> e=(nat m,0))"
proof -
 have first: "rho=1" and axis: "\<exists>e\<in>biv_support F. snd e=0"
   using positive_companion_first_weight_one[OF rho slope primitive Rhom Fhom face companion] by auto
 have sigma: "1<sigma" using slope first by simp
 have Fhom1: "weighted_homogeneous 1 (int sigma) (1+int sigma) F"
   using Fhom first by simp
 have Rhom1: "weighted_homogeneous 1 (int sigma) m R" using Rhom first by simp
 obtain f where f: "f\<in>biv_support F" and fy: "snd f=0" using axis by blast
 have f_weight: "pair_weight 1 (int sigma) f=1+int sigma"
   using Fhom1 f unfolding weighted_homogeneous_def by blast
 have fx_cast: "int(fst f)=int(sigma+1)"
   using f_weight fy by (simp add: pair_weight_def add.commute)
 have fx: "fst f=sigma+1" using fx_cast by simp
 have fpoint: "(sigma+1,0)\<in>biv_support F" using f fx fy by (cases f) simp
 let ?c="biv_coeff F (sigma+1) 0"
 let ?d="biv_coeff F 1 1"
 have c: "?c\<noteq>0" using fpoint by (simp add: biv_support_def)
 have subset: "e=(sigma+1,0) \<or> e=(1,1)" if "e\<in>biv_support F" for e
 proof -
   have restrict: "snd e=0 \<or> e=(1,1)"
     by (rule positive_companion_support_restrict[OF zero_less_one sigma, where F=F])
        (use Fhom1 that in auto)
   have at_e: "pair_weight 1 (int sigma) e=1+int sigma"
     using Fhom1 \<open>e\<in>biv_support F\<close> unfolding weighted_homogeneous_def by blast
   have "fst e=sigma+1" if "snd e=0"
     using at_e that by (simp add: pair_weight_def; arith)
   then show ?thesis using restrict by (cases e) auto
 qed
 have shape: "F=biv_monom ?c (sigma+1) 0+smult [:?d:] (biv_monom 1 1 1)"
 proof (rule biv_eqI)
   fix i j
   show "biv_coeff F i j=biv_coeff (biv_monom ?c (sigma+1) 0+smult [:?d:] (biv_monom 1 1 1)) i j"
   proof (cases "(i,j)=(sigma+1,0)")
     case True then show ?thesis by simp
   next
     case not_axis: False
     show ?thesis
     proof (cases "(i,j)=(1,1)")
       case True then show ?thesis by simp
     next
       case False
       have "(i,j)\<notin>biv_support F" using subset not_axis False by blast
       then show ?thesis using not_axis False by (auto simp: biv_support_def)
     qed
   qed
 qed
 have R: "R\<noteq>0" using face by auto
 have action: "biv_poisson R (biv_monom ?c (sigma+1) 0+smult [:?d:] (biv_monom 1 1 1))=R"
   by (rule trans[OF arg_cong[OF shape[symmetric], where f="\<lambda>S. biv_poisson R S"] companion])
 obtain e where e: "e\<in>biv_support R" and ey: "snd e=0"
   using positive_companion_root_has_axis_term_of_shape[OF c R action] by blast
 have e_weight: "pair_weight 1 (int sigma) e=m"
   using Rhom1 e unfolding weighted_homogeneous_def by blast
 have em: "int(fst e)=m" using e_weight ey by (simp add: pair_weight_def)
 have m: "0\<le>m" using em by arith
 have cast: "int(nat m)=m" using m by simp
 have ex: "fst e=nat m" using em cast by simp
 have endpoint: "(nat m,0)\<in>biv_support R" using e ex ey by (cases e) simp
 have bound: "fst z+snd z\<le>nat m" if "z\<in>biv_support R" for z
 proof -
   have weight: "int(fst z)+int sigma*int(snd z)=m"
     using Rhom1 that unfolding weighted_homogeneous_def
     by (auto simp: pair_weight_def)
   have sigma_one: "(1::int)\<le>int sigma" using sigma by simp
   have lower: "int(snd z)\<le>int sigma*int(snd z)"
     using mult_right_mono[OF sigma_one, of "int(snd z)"]
     by (simp only: mult_1_left; simp)
   have "int(fst z)+int(snd z)\<le>int(nat m)" using weight lower cast by linarith
   then show ?thesis by (simp only: of_nat_add[symmetric] of_nat_le_iff)
 qed
 have unique: "z=(nat m,0)" if z: "z\<in>biv_support R" and total: "fst z+snd z=nat m" for z
 proof -
   have weight: "int(fst z)+int sigma*int(snd z)=m"
     using Rhom1 z unfolding weighted_homogeneous_def
     by (auto simp: pair_weight_def)
   have degree: "int(fst z)+int(snd z)=m"
     using arg_cong[OF total, where f=int] cast
     by (simp only: of_nat_add)
   have product: "(int sigma-1)*int(snd z)=0"
   proof -
     have "(int sigma-1)*int(snd z)=
       (int(fst z)+int sigma*int(snd z))-(int(fst z)+int(snd z))"
       by (simp add: algebra_simps)
     also have "...=0" by (simp only: weight degree diff_self)
     finally show ?thesis .
   qed
   have sy: "snd z=0" using product sigma by auto
   have sx: "fst z=nat m" using total sy by simp
   show ?thesis using sx sy by (simp add: prod_eq_iff)
 qed
 show ?thesis using first endpoint bound unique by blast
qed

lemma positive_companion_root_power_has_axis_endpoint:
 fixes rho sigma k::nat and R F::"complex bivariate" and m::int
 assumes rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)" and companion: "biv_poisson R F=R"
 shows "(k*nat m,0)\<in>biv_support(R^k)"
proof -
 have data: "(nat m,0)\<in>biv_support R \<and>
   (\<forall>e\<in>biv_support R. fst e+snd e\<le>nat m) \<and>
   (\<forall>e\<in>biv_support R. fst e+snd e=nat m \<longrightarrow> e=(nat m,0))"
   using positive_companion_root_has_total_degree_endpoint[OF rho slope primitive Rhom Fhom face companion] by blast
 have bound: "pair_weight 1 1 e\<le>pair_weight 1 1 (nat m,0)" if "e\<in>biv_support R" for e
 proof -
   have natural: "fst e+snd e\<le>nat m" using data that by blast
   have integer: "int(fst e+snd e)\<le>int(nat m)" using natural by (simp only: of_nat_le_iff)
   show ?thesis using integer by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult_1_right of_nat_0 add_0_right of_nat_add)
 qed
 have unique: "e=(nat m,0)" if "e\<in>biv_support R" and "pair_weight 1 1 e=pair_weight 1 1 (nat m,0)" for e
 proof -
   have natural: "fst e+snd e=nat m" using that(2)
     by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult_1_right of_nat_0 add_0_right of_nat_add[symmetric] of_nat_eq_iff)
   show ?thesis using data that(1) natural by blast
 qed
 show ?thesis using corner_unique_top_power_endpoint[where R=R and rho=1 and sigma=1 and d="(nat m,0)" and m=k, OF conjunct1[OF data] bound unique]
   by (simp only: fst_conv snd_conv mult_zero_right)
qed

lemma positive_companion_leadingFace_has_axis_endpoint:
 fixes P::"complex poly_operator" and rho sigma k::nat and R F::"complex bivariate" and m::int and mu::complex
 assumes rho: "0<rho" and slope: "rho<sigma" and mu: "mu\<noteq>0" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)"
   and shape: "leading_form (int rho) (int sigma) P=smult [:mu:] (R^k)"
   and companion: "biv_poisson R F=R"
 shows "rho=1 \<and> (k*nat m,0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
proof -
 have first: "rho=1" using positive_companion_first_weight_one[OF rho slope primitive Rhom Fhom face companion] by blast
 have power: "(k*nat m,0)\<in>biv_support(R^k)"
   by (rule positive_companion_root_power_has_axis_endpoint[OF rho slope primitive Rhom Fhom face companion])
 have support: "biv_support(smult [:mu:] (R^k))=biv_support(R^k)"
   using mu by (auto simp: biv_support_def)
 have endpoint: "(k*nat m,0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
   using power by (simp only: shape support)
 show ?thesis using first endpoint by blast
qed
end
