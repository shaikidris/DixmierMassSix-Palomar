theory Coefficient_Density
  imports Coefficient_Recurrence
begin

lemma Comp_termCount_sq_ge:
  assumes h: "Comp rho s r f" and hs: "1\<le>s" and hsR: "s<rho"
    and hr0: "poly r 0=1" and hr: "0<degree r"
    and h1: "rootMultiplicity 1 r=2"
    and hother: "\<And>a. a\<noteq>1 \<Longrightarrow> rootMultiplicity a r\<le>1"
  shows "rho=s*degree r+1 \<and> 2*degree r+1\<le>termCount(r^2) \<and>
    (\<forall>j. coeff f j=of_real(recSeq s (degree r-1) j))"
proof -
  let ?L = "degree f"
  have hf: "0<degree f" by (rule Comp_natDegree_f_pos[OF h hsR hr0 hr])
  have fnz: "f\<noteq>0" using hf by auto
  have fact: "r=[:-1,1:]*f" by (rule Comp_eq_X_sub_one_mul[OF h hsR hr0 hr h1 hother])
  have degr: "degree r=?L+1" using fnz
    by (simp add: fact degree_mult_eq add.commute del: mult_pCons_left mult_pCons_right)
  have hid: "(rho-s)*degree r=1+rho*?L"
    by (rule Comp_degree_identity[OF h hsR hr hf])
  have rho: "rho=s*degree r+1" by (rule recurrence_degree_identity[OF hsR degr hid])
  have red: "[:of_nat rho-of_nat s:] * ([:0,1:]*f + [:0,1:]*euler f-euler f) =
    (f+[:of_nat rho:]*euler f+1)*[:0,1:]-(f+[:of_nat rho:]*euler f+1)"
    by (rule companion_factor_reduction[OF h fact fnz])
  have rec: "(1+of_nat s*(of_nat j+1))*coeff f (j+1) =
    -(of_nat s*(of_nat ?L-of_nat j))*coeff f j+(if j=0 then 1 else 0)" for j
    by (rule reduced_equation_coefficients[OF red]) (simp only: rho degr)
  have f0: "coeff f 0=-1" using Comp_f_eval_zero[OF h hr0] by (simp add: poly_0_coeff_0)
  have coeffs: "coeff f j=of_real(recSeq s ?L j)" for j
    by (rule recurrence_identifies_coefficients[OF f0 rec])
  define y where "y = (\<lambda>k. if k=0 then 1 else recSeq s ?L (k-1)-recSeq s ?L k)"
  have ry: "coeff r k=of_real(y k)" for k
    by (cases k) (simp_all add: fact y_def coeffs)
  have hL: "1\<le>?L" using hf by arith
  have sign: "0<(-1::real)^k*y k" if "k\<le>degree r" for k
    using recurrence_difference_sign[OF hs hL] that
    by (simp add: y_def degr)
  have tail: "y k=0" if "degree r<k" for k
  proof -
    have "coeff r k=0" by (rule coeff_eq_0[OF that])
    then show ?thesis by (simp add: ry)
  qed
  have count: "2*degree r+1\<le>termCount(r^2)"
    by (rule alternating_square_support[OF ry sign tail])
  show ?thesis using rho count coeffs by (simp add: degr)
qed

end
