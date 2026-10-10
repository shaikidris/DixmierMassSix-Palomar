theory One_Sided_Ratios
 imports "HOL-Computational_Algebra.Polynomial" "HOL.Rat"
begin
definition one_sided_ratio :: "nat\<times>nat \<Rightarrow> rat" where
 "one_sided_ratio p=of_nat(fst p)/(of_nat(snd p)-1)"
lemma one_sided_denominator_positive:
 assumes grade: "fst p<snd p" and ne: "p\<noteq>(0,1)"
 shows "1<snd p" and "0<(of_nat(snd p)::rat)-1"
proof -
 have j: "1<snd p"
 proof (rule ccontr)
  assume "\<not>1<snd p"
  then have "fst p=0" "snd p=1" using grade by arith+
  then have "p=(0,1)" by (simp add: prod_eq_iff)
  with ne show False by contradiction
 qed
 show "1<snd p" by fact
 have "(1::rat)<of_nat(snd p)" using j by simp
 then show "0<(of_nat(snd p)::rat)-1" by simp
qed
lemma one_sided_ratio_bounds:
 assumes grade: "fst p<snd p" and ne: "p\<noteq>(0,1)"
 shows "0\<le>one_sided_ratio p \<and> one_sided_ratio p\<le>1"
proof -
 have den: "0<(of_nat(snd p)::rat)-1" by (rule one_sided_denominator_positive(2)[OF grade ne])
 have le: "fst p+1\<le>snd p" using grade by arith
 have cast: "(of_nat(fst p+1)::rat)\<le>of_nat(snd p)" using le by simp
 have "(of_nat(fst p)::rat)+1\<le>of_nat(snd p)" using cast by simp
 then have num: "(of_nat(fst p)::rat)\<le>of_nat(snd p)-1" by linarith
 show ?thesis unfolding one_sided_ratio_def using den num
   by (simp add: divide_nonneg_pos divide_le_eq)
qed
lemma one_sided_ratio_eq_one_iff:
 assumes grade: "fst p<snd p" and ne: "p\<noteq>(0,1)"
 shows "one_sided_ratio p=1 \<longleftrightarrow> snd p=fst p+1"
proof -
 have den: "0<(of_nat(snd p)::rat)-1" by (rule one_sided_denominator_positive(2)[OF grade ne])
 have casts: "((of_nat(fst p)::rat)=of_nat(snd p)-1) \<longleftrightarrow> snd p=fst p+1"
 proof -
  have "((of_nat(fst p)::rat)=of_nat(snd p)-1) \<longleftrightarrow> of_nat(snd p)=(of_nat(fst p)::rat)+1" by linarith
  also have "... \<longleftrightarrow> (of_nat(snd p)::rat)=of_nat(fst p+1)" by (simp add: add.commute)
  also have "... \<longleftrightarrow> snd p=fst p+1" by (simp only: of_nat_eq_iff)
  finally show ?thesis .
 qed
 show ?thesis unfolding one_sided_ratio_def using den casts by (simp add: divide_eq_eq)
qed
lemma one_sided_support_extremal_ratio:
 assumes fin: "finite S" and grade: "\<forall>p\<in>S. fst p<snd p"
 and other: "\<exists>p\<in>S. p\<noteq>(0,1)"
 shows "\<exists>p\<in>S. p\<noteq>(0,1) \<and> 0\<le>one_sided_ratio p \<and> one_sided_ratio p\<le>1 \<and>
 (\<forall>q\<in>S. q\<noteq>(0,1) \<longrightarrow> one_sided_ratio q\<le>one_sided_ratio p)"
proof -
 let ?A="S-{(0,1)}"
 have f: "finite ?A" using fin by simp
 have ne: "?A\<noteq>{}" using other by auto
 have mem: "Max(one_sided_ratio ` ?A)\<in>one_sided_ratio ` ?A"
  by (rule Max_in) (use f ne in auto)
 obtain p where p: "p\<in>?A" and rev: "Max(one_sided_ratio ` ?A)=one_sided_ratio p"
  by (rule imageE[OF mem])
 have max: "one_sided_ratio p=Max(one_sided_ratio ` ?A)" by (rule rev[symmetric])
 have bounds: "0\<le>one_sided_ratio p \<and> one_sided_ratio p\<le>1"
  by (rule one_sided_ratio_bounds) (use p grade in auto)
 have top: "\<forall>q\<in>S. q\<noteq>(0,1) \<longrightarrow> one_sided_ratio q\<le>one_sided_ratio p"
 proof (intro ballI impI)
  fix q assume "q\<in>S" "q\<noteq>(0,1)"
  then have "one_sided_ratio q\<in>one_sided_ratio ` ?A" by auto
  then show "one_sided_ratio q\<le>one_sided_ratio p" unfolding max by (rule Max_ge[OF finite_imageI[OF f]])
 qed
 show ?thesis by (rule bexI[where x=p]) (use p bounds top in auto)
qed

lemma one_sided_support_ratio_dichotomy:
 assumes fin: "finite S" and grade: "\<forall>p\<in>S. fst p<snd p"
 and other: "\<exists>p\<in>S. p\<noteq>(0,1)"
 shows "(\<exists>p\<in>S. p\<noteq>(0,1) \<and> snd p=fst p+1) \<or>
 (\<exists>p\<in>S. p\<noteq>(0,1) \<and> one_sided_ratio p<1 \<and>
 (\<forall>q\<in>S. q\<noteq>(0,1) \<longrightarrow> one_sided_ratio q\<le>one_sided_ratio p))"
proof -
 obtain p where p: "p\<in>S" "p\<noteq>(0,1)" "0\<le>one_sided_ratio p" "one_sided_ratio p\<le>1"
 and top: "\<forall>q\<in>S. q\<noteq>(0,1) \<longrightarrow> one_sided_ratio q\<le>one_sided_ratio p"
  using one_sided_support_extremal_ratio[OF fin grade other] by blast
 show ?thesis
 proof (cases "one_sided_ratio p=1")
  case True
  have "snd p=fst p+1" using True one_sided_ratio_eq_one_iff[of p] grade p by auto
  then show ?thesis using p by blast
 next
  case False
  then have "one_sided_ratio p<1" using p(4) by arith
  then show ?thesis using p top by blast
 qed
qed
lemma one_sided_support_supporting_line:
 assumes fin: "finite S" and grade: "\<forall>p\<in>S. fst p<snd p"
 and other: "\<exists>p\<in>S. p\<noteq>(0,1)"
 shows "\<exists>t::rat. \<exists>p\<in>S. p\<noteq>(0,1) \<and> 0\<le>t \<and> t\<le>1 \<and>
 of_nat(fst p)=t*(of_nat(snd p)-1) \<and>
 (\<forall>q\<in>S. of_nat(fst q)\<le>t*(of_nat(snd q)-1))"
proof -
 obtain p where p: "p\<in>S" "p\<noteq>(0,1)" "0\<le>one_sided_ratio p" "one_sided_ratio p\<le>1"
 and top: "\<forall>q\<in>S. q\<noteq>(0,1) \<longrightarrow> one_sided_ratio q\<le>one_sided_ratio p"
  using one_sided_support_extremal_ratio[OF fin grade other] by blast
 have den: "0<(of_nat(snd p)::rat)-1" by (rule one_sided_denominator_positive(2)) (use grade p in auto)
 have eq: "of_nat(fst p)=one_sided_ratio p*(of_nat(snd p)-1)" using den by (simp add: one_sided_ratio_def)
 have line: "\<forall>q\<in>S. of_nat(fst q)\<le>one_sided_ratio p*(of_nat(snd q)-1)"
 proof (intro ballI)
  fix q assume q: "q\<in>S"
  show "of_nat(fst q)\<le>one_sided_ratio p*(of_nat(snd q)-1)"
  proof (cases "q=(0,1)")
   case True then show ?thesis by simp
  next
   case False
   have d: "0<(of_nat(snd q)::rat)-1" by (rule one_sided_denominator_positive(2)) (use grade q False in auto)
   have "one_sided_ratio q\<le>one_sided_ratio p" using top q False by blast
   then show ?thesis using d by (simp add: one_sided_ratio_def divide_le_eq)
  qed
 qed
 show ?thesis by (rule exI[where x="one_sided_ratio p"], rule bexI[where x=p]) (use p eq line in auto)
qed
lemma one_sided_support_face_dichotomy:
 assumes fin: "finite S" and grade: "\<forall>p\<in>S. fst p<snd p"
 and other: "\<exists>p\<in>S. p\<noteq>(0,1)"
 shows "(\<exists>p\<in>S. p\<noteq>(0,1) \<and> snd p=fst p+1) \<or>
 (\<exists>t::rat. \<exists>p\<in>S. p\<noteq>(0,1) \<and> 0\<le>t \<and> t<1 \<and>
 of_nat(fst p)=t*(of_nat(snd p)-1) \<and>
 (\<forall>q\<in>S. of_nat(fst q)\<le>t*(of_nat(snd q)-1)))"
proof -
 obtain t p where p: "p\<in>S" "p\<noteq>(0,1)" "0\<le>(t::rat)" "t\<le>1"
 and eq: "of_nat(fst p)=t*(of_nat(snd p)-1)"
 and line: "\<forall>q\<in>S. of_nat(fst q)\<le>t*(of_nat(snd q)-1)"
  using one_sided_support_supporting_line[OF fin grade other] by blast
 show ?thesis
 proof (cases "t=1")
  case True
  have cast: "(of_nat(snd p)::rat)=of_nat(fst p+1)" using eq True by (simp add: algebra_simps)
  have "snd p=fst p+1" using cast by (simp only: of_nat_eq_iff)
  then show ?thesis using p by blast
 next
  case False
  then have "t<1" using p(4) by arith
  then show ?thesis using p eq line by blast
 qed
qed

lemma one_sided_two_point_normal_sign:
 fixes rho sigma :: int and p :: "nat\<times>nat"
 assumes pos: "0<rho+sigma" and grade: "fst p<snd p" and ne: "p\<noteq>(0,1)"
 and weight: "rho*int(fst p)+sigma*int(snd p)=sigma"
 shows "0<rho \<and> sigma\<le>0 \<and> fst p+1<snd p"
proof -
 have j: "1<snd p" by (rule one_sided_denominator_positive(1)[OF grade ne])
 have gap: "fst p+1<snd p"
 proof (rule ccontr)
  assume "\<not>fst p+1<snd p"
  then have eq: "snd p=fst p+1" using grade by arith
  have cast: "int(snd p)=int(fst p)+1" using eq by simp
  have prod: "(rho+sigma)*int(fst p)=0" using weight unfolding cast by (simp add: algebra_simps)
  have "rho+sigma\<noteq>0" using pos by arith
  then have "fst p=0" using prod by simp
  then have "p=(0,1)" using eq by (simp add: prod_eq_iff)
  with ne show False by contradiction
 qed
 have sg: "sigma\<le>0"
 proof (rule ccontr)
  assume "\<not>sigma\<le>0"
  then have sp: "0<sigma" by arith
  have gp: "0<int(snd p)-1-int(fst p)" using gap by arith
  have first: "0\<le>(rho+sigma)*int(fst p)" by (rule mult_nonneg_nonneg) (use pos in auto)
  have second: "0<sigma*(int(snd p)-1-int(fst p))" by (rule mult_pos_pos[OF sp gp])
  have ident: "(rho+sigma)*int(fst p)+sigma*(int(snd p)-1-int(fst p))=0"
   using weight by (simp add: algebra_simps)
  show False using first second ident by arith
 qed
 show ?thesis using pos sg gap by arith
qed
lemma distinguished_ratio_control: "one_sided_ratio (0,1)=0"
 by (simp add: one_sided_ratio_def)
lemma boundary_ratio_control: "one_sided_ratio (1,2)=1"
 by (simp add: one_sided_ratio_def)
lemma vertical_ratio_control: "one_sided_ratio (0,2)=0"
 by (simp add: one_sided_ratio_def)
lemma signed_normal_control:
 "(2::int)+(-1)>0 \<and> (2::int)*1+(-1)*3=(-1)"
 by simp
end
