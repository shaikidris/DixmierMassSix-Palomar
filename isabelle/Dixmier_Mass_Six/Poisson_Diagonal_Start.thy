theory Poisson_Diagonal_Start
 imports "Poisson_Endpoint_Maximizers"
   "Weighted_Contraction_Bounds"
   "Weighted_Newton_Definitions"
begin

lemma exponent_eq_of_grade_and_weight:
 fixes rho sigma::int and d e::"nat\<times>nat"
 assumes sum: "rho+sigma\<noteq>0" and grade: "pair_grade d=pair_grade e"
 and weight: "pair_weight rho sigma d=pair_weight rho sigma e"
 shows "d=e"
proof -
 have g: "int(fst d)-int(snd d)=int(fst e)-int(snd e)" using grade by (simp add: pair_grade_def)
 have w: "rho*int(fst d)+sigma*int(snd d)=rho*int(fst e)+sigma*int(snd e)"
   using weight by (simp add: pair_weight_def mult.commute)
 have product: "(int(fst d)-int(fst e))*(rho+sigma)=0"
 proof -
   have scaled: "sigma*(int(fst d)-int(snd d))=sigma*(int(fst e)-int(snd e))"
     using arg_cong[OF g, of "\<lambda>z. sigma*z"] .
   show ?thesis using scaled w by (simp add: algebra_simps; linarith)
 qed
 have fx: "fst d=fst e" using product sum by auto
 have sy: "snd d=snd e" using fx g by auto
 show ?thesis using fx sy by (simp add: prod_eq_iff)
qed

lemma corner_diagonal_weight_eq_grade:
 "pair_weight 1 (-1) d=pair_grade d"
 by (simp add: pair_weight_def pair_grade_def)

lemma poisson_support_weight_le:
 fixes R F::"complex bivariate"
 assumes R: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x\<le>m"
 and F: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_weight rho sigma x\<le>n"
 and e: "e\<in>biv_support(biv_poisson R F)"
 shows "pair_weight rho sigma e\<le>m+n-(rho+sigma)"
 by (rule poisson_support_bound[OF R F e])

lemma poisson_companion_top_grade_nonnegative:
 fixes R F::"complex bivariate"
 assumes companion: "biv_poisson R F=R" and d: "d\<in>biv_support R"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x\<le>pair_grade d"
 and emax: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x\<le>pair_grade e"
 shows "0\<le>pair_grade e"
proof -
 have db: "d\<in>biv_support(biv_poisson R F)" using d companion by simp
 have Rb: "pair_weight 1 (-1) x\<le>pair_grade d" if "x\<in>biv_support R" for x
   using dmax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
 have Fb: "pair_weight 1 (-1) x\<le>pair_grade e" if "x\<in>biv_support F" for x
   using emax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
 have bound: "pair_weight 1 (-1) d\<le>pair_grade d+pair_grade e-(1+(-1))"
   by (rule poisson_support_weight_le[OF Rb Fb db])
 show ?thesis using bound by (simp only: corner_diagonal_weight_eq_grade; arith)
qed

lemma poisson_companion_unique_top_not_collinear:
 fixes rho sigma::int and R F::"complex bivariate"
 assumes companion: "biv_poisson R F=R"
 and d: "d\<in>biv_support R" and e: "e\<in>biv_support F"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma d"
 and emax: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma e"
 and du: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x=pair_weight rho sigma d \<Longrightarrow> x=d"
 and eu: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_weight rho sigma x=pair_weight rho sigma e \<Longrightarrow> x=e"
 and degree: "pair_weight rho sigma e=rho+sigma"
 shows "(of_nat(snd d)::complex)* of_nat(fst e)- of_nat(fst d)* of_nat(snd e)\<noteq>0"
proof
 assume parallel: "(of_nat(snd d)::complex)* of_nat(fst e)- of_nat(fst d)* of_nat(snd e)=0"
 have Rt: "weighted_component rho sigma (pair_weight rho sigma d) R=biv_monom(biv_coeff R (fst d)(snd d))(fst d)(snd d)"
   by (rule endpoint_unique_top_component[OF d du])
 have Ft: "weighted_component rho sigma (pair_weight rho sigma e) F=biv_monom(biv_coeff F (fst e)(snd e))(fst e)(snd e)"
   by (rule endpoint_unique_top_component[OF e eu])
 have index: "pair_weight rho sigma d+pair_weight rho sigma e-(rho+sigma)=pair_weight rho sigma d"
   using degree by arith
 have topformula: "weighted_component rho sigma
   (pair_weight rho sigma d+pair_weight rho sigma e-(rho+sigma)) (biv_poisson R F)=
   biv_poisson (weighted_component rho sigma (pair_weight rho sigma d) R)
     (weighted_component rho sigma (pair_weight rho sigma e) F)"
   by (rule poisson_weighted_component_of_bounds[OF dmax emax])
 have monomial_zero: "biv_poisson
   (biv_monom(biv_coeff R (fst d)(snd d))(fst d)(snd d))
   (biv_monom(biv_coeff F (fst e)(snd e))(fst e)(snd e))=0"
   by (simp add: poisson_monomial_general parallel)
 have top: "weighted_component rho sigma (pair_weight rho sigma d) R=0"
   using topformula monomial_zero by (simp only: index companion Rt Ft)
 have coeff: "biv_coeff R (fst d)(snd d)\<noteq>0" using d by (simp add: biv_support_def)
 show False using top coeff by (simp add: Rt)
qed

lemma poisson_companion_no_two_diagonal_tops:
 fixes R F::"complex bivariate"
 assumes companion: "biv_poisson R F=R" and d: "d\<in>biv_support R" and e: "e\<in>biv_support F"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x\<le>pair_grade d"
 and emax: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x\<le>pair_grade e"
 and du: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x=pair_grade d \<Longrightarrow> x=d"
 and eu: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x=pair_grade e \<Longrightarrow> x=e"
 and dd: "fst d=snd d" and ed: "fst e=snd e"
 shows False
proof -
 have dmaxw: "pair_weight 1 (-1) x\<le>pair_weight 1 (-1) d" if "x\<in>biv_support R" for x
   using dmax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
 have emaxw: "pair_weight 1 (-1) x\<le>pair_weight 1 (-1) e" if "x\<in>biv_support F" for x
   using emax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
 have duw: "x=d" if "x\<in>biv_support R" and "pair_weight 1 (-1) x=pair_weight 1 (-1) d" for x
   using du that by (simp only: corner_diagonal_weight_eq_grade; blast)
 have euw: "x=e" if "x\<in>biv_support F" and "pair_weight 1 (-1) x=pair_weight 1 (-1) e" for x
   using eu that by (simp only: corner_diagonal_weight_eq_grade; blast)
 have degree: "pair_weight 1 (-1) e=1+(-1)" by (simp add: pair_weight_def ed)
 have ne: "(of_nat(snd d)::complex)* of_nat(fst e)- of_nat(fst d)* of_nat(snd e)\<noteq>0"
   by (rule poisson_companion_unique_top_not_collinear[OF companion d e dmaxw emaxw duw euw degree])
 show False using ne by (simp add: dd ed)
qed

lemma poisson_companion_no_diagonal_unique_top:
 fixes R F::"complex bivariate"
 assumes companion: "biv_poisson R F=R" and d: "d\<in>biv_support R" and e: "e\<in>biv_support F"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x\<le>pair_grade d"
 and emax: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x\<le>pair_grade e"
 and du: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x=pair_grade d \<Longrightarrow> x=d"
 and eu: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x=pair_grade e \<Longrightarrow> x=e"
 and dd: "fst d=snd d" and dp: "0<fst d"
 shows False
proof -
 have dg: "pair_grade d=0" by (simp add: pair_grade_def dd)
 have eg: "0\<le>pair_grade e" by (rule poisson_companion_top_grade_nonnegative[OF companion d dmax emax])
 show False
 proof (cases "pair_grade e=0")
   case True
   have ed: "fst e=snd e" using True by (simp add: pair_grade_def)
   show False by (rule poisson_companion_no_two_diagonal_tops[OF companion d e dmax emax du eu dd ed])
 next
   case False
   have ep: "0<pair_grade e" using eg False by arith
   have topR: "weighted_component 1 (-1) (pair_grade e) R=0"
   proof (rule biv_eqI)
     fix i j
     have zero: "pair_weight 1 (-1) (i,j)=pair_grade e \<Longrightarrow> biv_coeff R i j=0"
     proof -
       assume w: "pair_weight 1 (-1) (i,j)=pair_grade e"
       show "biv_coeff R i j=0"
       proof (rule ccontr)
         assume "biv_coeff R i j\<noteq>0"
         then have member: "(i,j)\<in>biv_support R" by (simp add: biv_support_def)
         have "pair_grade (i,j)\<le>0" using dmax[OF member] dg by simp
         then show False using w ep by (simp only: corner_diagonal_weight_eq_grade; arith)
       qed
     qed
     show "biv_coeff(weighted_component 1 (-1) (pair_grade e) R) i j=biv_coeff 0 i j"
       using zero by (simp add: weighted_component_coeff)
   qed
   have top: "weighted_component 1 (-1) (pair_weight 1 (-1) d+pair_weight 1 (-1) e-(1+(-1))) (biv_poisson R F)=0"
     by (simp only: companion corner_diagonal_weight_eq_grade dg; simp add: topR)
   have dmaxw: "pair_weight 1 (-1) x\<le>pair_weight 1 (-1) d" if "x\<in>biv_support R" for x
     using dmax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
   have emaxw: "pair_weight 1 (-1) x\<le>pair_weight 1 (-1) e" if "x\<in>biv_support F" for x
     using emax[OF that] by (simp only: corner_diagonal_weight_eq_grade)
   have duw: "x=d" if "x\<in>biv_support R" and "pair_weight 1 (-1) x=pair_weight 1 (-1) d" for x
     using du that by (simp only: corner_diagonal_weight_eq_grade; blast)
   have euw: "x=e" if "x\<in>biv_support F" and "pair_weight 1 (-1) x=pair_weight 1 (-1) e" for x
     using eu that by (simp only: corner_diagonal_weight_eq_grade; blast)
   have col: "(of_nat(snd d)::complex)* of_nat(fst e)- of_nat(fst d)* of_nat(snd e)=0"
     by (rule poisson_unique_maximizers_collinear_of_top_zero[OF top d e dmaxw emaxw duw euw])
   have dn: "(of_nat(snd d)::complex)\<noteq>0" using dp dd by simp
   have product: "(of_nat(snd d)::complex)*(of_nat(fst e)- of_nat(snd e))=0"
     using col by (simp add: dd algebra_simps)
   have equal: "(of_nat(fst e)::complex)= of_nat(snd e)" using product dn by auto
   have ed: "fst e=snd e" using equal by (simp only: of_nat_eq_iff)
   show False using ep by (simp add: pair_grade_def ed)
 qed
qed

lemma poisson_companion_no_diagonal_homogeneous_top:
 fixes rho sigma m n::int and R F::"complex bivariate"
 assumes sum: "rho+sigma\<noteq>0"
 and Rhom: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x=m"
 and Fhom: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_weight rho sigma x=n"
 and companion: "biv_poisson R F=R" and d: "d\<in>biv_support R" and e: "e\<in>biv_support F"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x\<le>pair_grade d"
 and emax: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_grade x\<le>pair_grade e"
 and dd: "fst d=snd d" and dp: "0<fst d"
 shows False
proof -
 have du: "x=d" if x: "x\<in>biv_support R" and g: "pair_grade x=pair_grade d" for x
   by (rule exponent_eq_of_grade_and_weight[OF sum g]) (use Rhom[OF x] Rhom[OF d] in simp)
 have eu: "x=e" if x: "x\<in>biv_support F" and g: "pair_grade x=pair_grade e" for x
   by (rule exponent_eq_of_grade_and_weight[OF sum g]) (use Fhom[OF x] Fhom[OF e] in simp)
 show False by (rule poisson_companion_no_diagonal_unique_top[OF companion d e dmax emax du eu dd dp])
qed

lemma poisson_companion_no_diagonal_homogeneous_max:
 fixes rho sigma m n::int and R F::"complex bivariate"
 assumes sum: "rho+sigma\<noteq>0"
 and Rhom: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x=m"
 and Fhom: "\<And>x. x\<in>biv_support F \<Longrightarrow> pair_weight rho sigma x=n"
 and companion: "biv_poisson R F=R" and d: "d\<in>biv_support R"
 and dmax: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_grade x\<le>pair_grade d"
 and dd: "fst d=snd d" and dp: "0<fst d"
 shows False
proof -
 have Rnz: "R\<noteq>0" using d by auto
 have Fnz: "F\<noteq>0" using companion Rnz by (auto simp: biv_poisson_def)
 have nonempty: "biv_support F\<noteq>{}" using Fnz by simp
 have maximum: "Max(pair_grade ` biv_support F)\<in>pair_grade ` biv_support F"
   by (rule Max_in) (use nonempty in auto)
 obtain e where e: "e\<in>biv_support F" and max: "pair_grade e=Max(pair_grade ` biv_support F)" using maximum by auto
 have emax: "pair_grade x\<le>pair_grade e" if "x\<in>biv_support F" for x
   unfolding max by (rule Max_ge) (use that in auto)
 show False by (rule poisson_companion_no_diagonal_homogeneous_top[OF sum Rhom Fhom companion d e dmax emax dd dp])
qed
end
