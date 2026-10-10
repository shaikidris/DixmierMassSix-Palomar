theory Horizontal_Companion
 imports "General_Root_Degree"
   "Scalar_Classification"
   "Sparse_Root_Order"
   "Crossing_Expand_Multiplicity"
begin

definition HorizComp::"nat \<Rightarrow> complex poly \<Rightarrow> complex poly \<Rightarrow> bool" where
 "HorizComp a g f \<longleftrightarrow> f*pderiv g-[:of_nat a:]*pderiv f*g=g"

lemma HorizComp_natDegree_f_pos:
 assumes h: "HorizComp a g f" and g: "0<degree g"
 shows "0<degree f"
proof (rule ccontr)
 assume "\<not>0<degree f"
 then have fzero: "degree f=0" by simp
 obtain c where fc: "f=[:c:]" using degree_eq_zeroE[OF fzero] by blast
 have eq: "[:c:]*pderiv g=g" using h by (simp add: HorizComp_def fc pderiv_pCons)
 have scalar: "smult c (pderiv g)=g" using eq by simp
 have bound: "degree g\<le>degree(pderiv g)"
 proof -
   have "degree g=degree(smult c (pderiv g))" by (rule arg_cong[OF scalar[symmetric]])
   also have "...\<le>degree(pderiv g)" by (rule degree_smult_le)
   finally show ?thesis .
 qed
 show False using bound g by (simp add: degree_pderiv)
qed

lemma HorizComp_root_slope:
 fixes g f::"complex poly"
 assumes h: "HorizComp a g f" and g: "g\<noteq>0" and root: "poly g beta=0"
 shows "poly f beta=0 \<and> (of_nat(rootMultiplicity beta g)-of_nat a)*poly(pderiv f)beta=1"
proof -
 have jpos: "0<order beta g" using root order_gt_0_iff[OF g] by simp
 obtain k where jk: "order beta g=Suc k" using jpos by (cases "order beta g") auto
 obtain u where gu: "g=[:-beta,1:]^Suc k*u" and und: "\<not>[:-beta,1:] dvd u"
   using order_decomp[OF g, of beta] unfolding jk by blast
 have unz: "poly u beta\<noteq>0" using und by (simp add: poly_eq_0_iff_dvd)
 let ?B="[:-beta,1:]"
 let ?D="[:of_nat(Suc k):]*u+?B*pderiv u"
 have bnz: "?B\<noteq>0" by simp
 have bknz: "?B^k\<noteq>0" using bnz by simp
 have dg: "pderiv g=?B^k*?D"
   unfolding gu pderiv_mult pderiv_power_Suc
   by (simp add: pderiv_pCons algebra_simps smult_add_right smult_diff_right)
 have e1: "?B^k*(f*?D-[:of_nat a:]*pderiv f*?B*u)=?B^k*(?B*u)"
 proof -
   have "?B^k*(f*?D-[:of_nat a:]*pderiv f*?B*u)=f*pderiv g-[:of_nat a:]*pderiv f*g"
     by (simp only: dg; simp only: gu power_Suc; algebra)
   also have "...=g" by (rule h[unfolded HorizComp_def])
   also have "...=?B^k*(?B*u)" by (simp only: gu power_Suc; algebra)
   finally show ?thesis .
 qed
 have one: "f*?D-[:of_nat a:]*pderiv f*?B*u=?B*u"
   using e1 by (simp only: mult_left_cancel[OF bknz])
 have eval: "poly f beta*(of_nat(Suc k)*poly u beta)=0"
   using arg_cong[where f="\<lambda>p. poly p beta", OF one] by simp
 have successor_nonzero: "(of_nat(Suc k)::complex)\<noteq>0"
   by (simp only: of_nat_eq_0_iff Suc_not_Zero not_False_eq_True)
 have fa: "poly f beta=0" using eval successor_nonzero unz
   by (auto simp only: mult_eq_0_iff)
 obtain v where fv: "f=?B*v" using fa unfolding poly_eq_0_iff_dvd dvd_def by blast
 have df: "pderiv f=v+?B*pderiv v" unfolding fv pderiv_mult by (simp add: pderiv_pCons)
 have e2: "?B*(v*?D-[:of_nat a:]*(v+?B*pderiv v)*u)=?B*u"
 proof -
   have "?B*(v*?D-[:of_nat a:]*(v+?B*pderiv v)*u)=f*?D-[:of_nat a:]*pderiv f*?B*u"
     by (simp only: df; simp only: fv; algebra)
   also have "...=?B*u" by (rule one)
   finally show ?thesis .
 qed
 have two: "v*?D-[:of_nat a:]*(v+?B*pderiv v)*u=u"
   using e2 by (simp only: mult_left_cancel[OF bnz])
 have evaluated: "poly v beta*(of_nat(Suc k)*poly u beta)-of_nat a*poly v beta*poly u beta=poly u beta"
   using arg_cong[where f="\<lambda>p. poly p beta", OF two] by (simp add: mult.assoc)
 have calculation: "(b*(j*u)-a*b*u)-u=((j-a)*b-1)*u" for a b j u::complex by algebra
 have product: "((of_nat(Suc k)-of_nat a)*poly v beta-1)*poly u beta=0"
   using evaluated by (simp only: calculation[symmetric] diff_self)
 have slope: "(of_nat(Suc k)-of_nat a)*poly v beta=1" using product unz by auto
 show ?thesis using slope fa g by (simp add: df rootMultiplicity_eq_order jk)
qed

lemma HorizComp_degree_identity_of_f_degree_ge_two:
 fixes g f::"complex poly"
 assumes h: "HorizComp a g f" and g: "0<degree g" and f: "2\<le>degree f"
 shows "degree g=a*degree f"
proof -
 let ?e="degree g" let ?L="degree f"
 have gnz: "g\<noteq>0" using g by auto
 have fnz: "f\<noteq>0" using f by auto
 have lead: "coeff f ?L*coeff g ?e\<noteq>0" using fnz gnz by simp
 have index: "?L+(?e-1)=(?L-1)+?e" using g f by arith
 have left: "coeff(f*pderiv g)((?L-1)+?e)=coeff f ?L*coeff(pderiv g)(?e-1)"
   by (simp only: index[symmetric]; rule coeff_mult_of_degree_le) (simp_all add: degree_pderiv)
 have right: "coeff(pderiv f*g)((?L-1)+?e)=coeff(pderiv f)(?L-1)*coeff g ?e"
   by (rule coeff_mult_of_degree_le) (simp_all add: degree_pderiv)
 have above: "coeff g ((?L-1)+?e)=0" by (rule coeff_eq_0) (use f in arith)
 have df: "coeff(pderiv f)(?L-1)=of_nat ?L*coeff f ?L" using f by (simp add: coeff_pderiv)
 have dg: "coeff(pderiv g)(?e-1)=of_nat ?e*coeff g ?e" using g by (simp add: coeff_pderiv)
 have scalar_product: "[:of_nat a:]*pderiv f*g=smult (of_nat a) (pderiv f*g)" by simp
 have raw: "coeff(f*pderiv g-[:of_nat a:]*pderiv f*g)((?L-1)+?e)=coeff g ((?L-1)+?e)"
   by (rule arg_cong[where f="\<lambda>p. coeff p ((?L-1)+?e)", OF h[unfolded HorizComp_def]])
 have expanded: "coeff(f*pderiv g)((?L-1)+?e)-of_nat a*coeff(pderiv f*g)((?L-1)+?e)=coeff g ((?L-1)+?e)"
   using raw by (simp only: scalar_product coeff_diff coeff_smult)
 have eq: "coeff f ?L*(of_nat ?e*coeff g ?e)-of_nat a*((of_nat ?L*coeff f ?L)*coeff g ?e)=0"
   using expanded by (simp only: left right above df dg)
 have calculation: "b*(e*c)-a*((L*b)*c)=(e-a*L)*(b*c)" for a b c e L::complex by algebra
 have cast: "(of_nat ?e::complex)=of_nat a*of_nat ?L" using eq lead by (simp only: calculation; auto)
 show ?thesis using cast by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
qed

lemma HorizComp_exists_rootMultiplicity_gt_a:
 assumes h: "HorizComp a g f" and g: "0<degree g" and a: "a<degree g"
 shows "\<exists>beta. poly g beta=0 \<and> a<rootMultiplicity beta g"
proof -
 have f: "0<degree f" by (rule HorizComp_natDegree_f_pos[OF h g])
 have gnz: "g\<noteq>0" using g by auto
 have fnz: "f\<noteq>0" using f by auto
 obtain beta where root: "poly g beta=0" and max: "\<forall>z. poly g z=0 \<longrightarrow> rootMultiplicity z g\<le>rootMultiplicity beta g"
   using exists_max_rootMultiplicity[OF g] by blast
 have roots: "poly f z=0" if "poly g z=0" for z using HorizComp_root_slope[OF h gnz that] by blast
 have maximum: "rootMultiplicity z g\<le>rootMultiplicity beta g" if root_z: "poly g z=0" for z
   by (rule mp[OF spec[OF max, of z] root_z])
 have bound: "degree g\<le>rootMultiplicity beta g*degree f"
   by (rule degree_le_maxMultiplicity_mul_companionDegree[OF gnz fnz roots maximum])
 have different: "rootMultiplicity beta g\<noteq>a" using HorizComp_root_slope[OF h gnz root] by auto
 have lower: "a\<le>rootMultiplicity beta g"
 proof (cases "degree f=1")
   case True show ?thesis using bound a True by simp
 next
   case False
   have large: "2\<le>degree f" using False f by arith
   have equality: "degree g=a*degree f" by (rule HorizComp_degree_identity_of_f_degree_ge_two[OF h g large])
   show ?thesis using bound f by (simp only: equality mult_le_cancel_right; auto)
 qed
 show ?thesis using root lower different by auto
qed

lemma HorizComp_exists_nonzero_rootMultiplicity_gt_a:
 assumes h: "HorizComp a g f" and g: "0<degree g" and a: "a<degree g" and zero: "rootMultiplicity 0 g<a"
 shows "\<exists>beta. beta\<noteq>0 \<and> poly g beta=0 \<and> a<rootMultiplicity beta g"
proof -
 obtain beta where root: "poly g beta=0" and greater: "a<rootMultiplicity beta g"
   using HorizComp_exists_rootMultiplicity_gt_a[OF h g a] by blast
 have nonzero: "beta\<noteq>0"
 proof
   assume beta_zero: "beta=0"
   have "a<rootMultiplicity 0 g" using greater by (simp only: beta_zero)
   then show False using zero by arith
 qed
 show ?thesis by (rule exI[of _ beta]) (rule conjI[OF nonzero conjI[OF root greater]])
qed

lemma power_rootMultiplicity_lt_termCount:
 fixes g::"complex poly"
 assumes g: "g\<noteq>0" and beta: "beta\<noteq>0"
 shows "k*rootMultiplicity beta g<termCount(g^k)"
proof -
 have power: "g^k\<noteq>0" using g by simp
 show ?thesis using rootMultiplicity_lt_termCount[OF power beta]
   by (simp only: rootMultiplicity_eq_order[OF power, symmetric] native_rootMultiplicity_power)
qed

lemma HorizComp_mass_six_parameters:
 assumes h: "HorizComp a g f" and g: "0<degree g" and a: "a<degree g" and zero: "rootMultiplicity 0 g<a"
 and k: "2\<le>k" and terms: "termCount(g^k)\<le>6"
 shows "k=2 \<and> a=1 \<and> (\<exists>beta. beta\<noteq>0 \<and> poly g beta=0 \<and> rootMultiplicity beta g=2)"
proof -
 obtain beta where beta: "beta\<noteq>0" and root: "poly g beta=0" and greater: "a<rootMultiplicity beta g"
   using HorizComp_exists_nonzero_rootMultiplicity_gt_a[OF h g a zero] by blast
 have gnz: "g\<noteq>0" using g by auto
 have product: "k*rootMultiplicity beta g<6" using power_rootMultiplicity_lt_termCount[OF gnz beta, of k] terms by arith
 have apositive: "0<a" using zero by arith
 have two: "2\<le>rootMultiplicity beta g" using greater apositive by arith
 have boundq: "2*rootMultiplicity beta g\<le>k*rootMultiplicity beta g" by (rule mult_le_mono1[OF k])
 have boundk: "k*2\<le>k*rootMultiplicity beta g" by (rule mult_le_mono2[OF two])
 have q: "rootMultiplicity beta g=2" using product boundq two by arith
 have exponent: "k=2" using product boundk k by arith
 have base: "a=1" using greater q apositive by arith
 show ?thesis using exponent base beta root q by blast
qed

lemma HorizComp_all_roots_double:
 assumes h: "HorizComp 1 g f" and g: "0<degree g" and zero: "rootMultiplicity 0 g<1"
 and terms: "termCount(g^2)\<le>6"
 shows "\<forall>beta. poly g beta=0 \<longrightarrow> rootMultiplicity beta g=2"
proof -
 have gnz: "g\<noteq>0" using g by auto
 have count_zero: "rootMultiplicity 0 g=0" using zero by arith
 have order_zero: "order (0::complex) g=0"
   using count_zero by (simp only: rootMultiplicity_eq_order[OF gnz])
 have zero_equivalence: "0<order (0::complex) g \<longleftrightarrow> poly g 0=0"
   by (rule order_gt_0_iff[OF gnz])
 have gzero: "poly g 0\<noteq>0" using zero_equivalence by (simp add: order_zero)
 show ?thesis
 proof (intro allI impI)
   fix beta assume root: "poly g beta=0"
   have order_positive: "0<order beta g" by (rule iffD2[OF order_gt_0_iff[OF gnz] root])
   have positive: "0<rootMultiplicity beta g"
     using order_positive by (simp only: rootMultiplicity_eq_order[OF gnz])
   have upper: "rootMultiplicity beta g\<le>2" by (rule rootMultiplicity_le_two[OF gzero terms])
   have different: "rootMultiplicity beta g\<noteq>1" using HorizComp_root_slope[OF h gnz root] by auto
   show "rootMultiplicity beta g=2" using positive upper different by arith
 qed
qed

end
