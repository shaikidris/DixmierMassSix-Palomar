theory Companion_Nonmonomial
 imports Homogeneous_Power_Endpoints
begin

lemma poisson_xy_eq_negative_grade_euler:
 fixes R::"complex bivariate"
 shows "biv_poisson R (biv_monom 1 1 1)=biv_monom 1 0 1*biv_dy R-biv_monom 1 1 0*biv_dx R"
 by (simp add: biv_poisson_def biv_dx_monom biv_dy_monom mult.commute)

lemma corner_y_times_dy_coeff:
 "biv_coeff(biv_monom 1 0 1*biv_dy R) i j= of_nat j*biv_coeff R i j" for R::"complex bivariate"
 by (cases j) (simp_all add: biv_coeff_def biv_monom_def coeff_monom_mult biv_dy_def coeff_pderiv of_nat_poly one_pCons)

lemma corner_x_times_dx_coeff:
 "biv_coeff(biv_monom 1 1 0*biv_dx R) i j= of_nat i*biv_coeff R i j" for R::"complex bivariate"
 by (cases i) (simp_all add: biv_coeff_def biv_monom_def coeff_monom_mult biv_dx_def coeff_map_poly coeff_pderiv)

lemma poisson_xy_coeff:
 fixes R::"complex bivariate" and e::"nat\<times>nat"
 shows "biv_coeff(biv_poisson R (biv_monom 1 1 1)) (fst e)(snd e)=
   (of_nat(snd e)- of_nat(fst e))*biv_coeff R (fst e)(snd e)"
 by (simp only: poisson_xy_eq_negative_grade_euler biv_coeff_diff corner_y_times_dy_coeff corner_x_times_dx_coeff; algebra)

lemma corner_poisson_smult_right:
 "biv_poisson R (smult [:c:] F)=smult [:c:] (biv_poisson R F)" for R F::"complex bivariate"
proof -
 have dx: "biv_dx(smult [:c:] F)=smult [:c:] (biv_dx F)"
   by (rule biv_eqI) (simp add: biv_dx_coeff)
 have dy: "biv_dy(smult [:c:] F)=smult [:c:] (biv_dy F)"
   by (rule biv_eqI) (simp add: biv_dy_coeff)
 have scalar: "smult [:c:] p=[:[:c:]:]*p" for p::"complex bivariate" by simp
 show ?thesis by (simp only: biv_poisson_def dx dy mult_smult_right smult_diff_right)
qed

lemma crossing_poisson_companion_nonmonomial:
 fixes R F::"complex bivariate" and a b::"nat\<times>nat"
 assumes base: "(1,1)\<in>biv_support F" and companion: "biv_poisson R F=R"
 and a: "a\<in>biv_support R" and b: "b\<in>biv_support R"
 and apos: "0<pair_grade a" and bneg: "pair_grade b<0"
 shows "1<card(biv_support F)"
proof (rule ccontr)
 assume no: "\<not>1<card(biv_support F)"
 have unique: "e=(1,1)" if "e\<in>biv_support F" for e
 proof -
   have card: "card(biv_support F)\<le>1" using no by arith
   have same: "\<forall>x\<in>biv_support F. \<forall>y\<in>biv_support F. x=y"
     using card_le_Suc0_iff_eq[where A="biv_support F", OF finite_biv_support] card by simp
   show ?thesis by (rule bspec[OF bspec[OF same that] base])
 qed
 let ?c="biv_coeff F 1 1"
 have c: "?c\<noteq>0" using base by (simp add: biv_support_def)
 have monomial: "F=biv_monom ?c 1 1"
 proof (rule biv_eqI)
   fix i j
   show "biv_coeff F i j=biv_coeff(biv_monom ?c 1 1) i j"
   proof (cases "(i,j)=(1,1)")
     case True then show ?thesis by simp
   next
     case False
     have absent: "(i,j)\<notin>biv_support F" using unique False by blast
     have zero: "biv_coeff F i j=0" using absent by (simp add: biv_support_def)
     have condition: "\<not>(i=1 \<and> j=1)" using False by auto
     show ?thesis by (simp only: biv_coeff_monom condition if_False zero)
   qed
 qed
 have scaled: "F=smult [:?c:] (biv_monom 1 1 1)" using monomial by (simp only: endpoint_biv_smult_monom mult_1_right)
 have action: "biv_poisson R F=smult [:?c:] (biv_poisson R (biv_monom 1 1 1))"
   by (rule trans[OF arg_cong[where f="biv_poisson R", OF scaled] corner_poisson_smult_right])
 have coefficient: "?c*(of_nat(snd e)- of_nat(fst e))=1" if e: "e\<in>biv_support R" for e
 proof -
   have nonzero: "biv_coeff R (fst e)(snd e)\<noteq>0" using e by (simp add: biv_support_def)
   have action_coeff: "biv_coeff(biv_poisson R F)(fst e)(snd e)=
     ?c*biv_coeff(biv_poisson R (biv_monom 1 1 1))(fst e)(snd e)"
     using arg_cong[where f="\<lambda>p. biv_coeff p (fst e)(snd e)", OF action]
     by (simp only: biv_coeff_smult)
   have companion_coeff: "biv_coeff(biv_poisson R F)(fst e)(snd e)=biv_coeff R (fst e)(snd e)"
     by (rule arg_cong[where f="\<lambda>p. biv_coeff p (fst e)(snd e)", OF companion])
   have xy: "biv_coeff(biv_poisson R (biv_monom 1 1 1))(fst e)(snd e)=
     (of_nat(snd e)-of_nat(fst e))*biv_coeff R (fst e)(snd e)"
     by (rule poisson_xy_coeff[where R=R and e=e])
   have scalar_equality: "?c*((of_nat(snd e)-of_nat(fst e))*biv_coeff R (fst e)(snd e))=
     biv_coeff R (fst e)(snd e)"
     using action_coeff companion_coeff by (simp only: xy; blast)
   have equality: "(?c*(of_nat(snd e)- of_nat(fst e)))*biv_coeff R (fst e)(snd e)=
     1*biv_coeff R (fst e)(snd e)"
     using scalar_equality by (simp only: mult.assoc mult_1_left)
   show ?thesis using equality nonzero by simp
 qed
 have equal: "(of_nat(snd a)::complex)- of_nat(fst a)= of_nat(snd b)- of_nat(fst b)"
   using coefficient[OF a] coefficient[OF b] c by (metis mult_left_cancel)
 have casts: "(of_int (int(snd a)-int(fst a))::complex)= of_int (int(snd b)-int(fst b))"
   using equal by simp
 have integer: "int(snd a)-int(fst a)=int(snd b)-int(fst b)"
   using casts by (simp only: of_int_eq_iff)
 show False using integer apos bneg by (simp add: pair_grade_def; arith)
qed
end
