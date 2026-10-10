theory Mate_Power_Arithmetic
 imports "Bivariate_Ratio"
begin

text \<open>For a nonzero univariate polynomial, native order at zero is
exactly the source natTrailingDegree. The source assumptions on nonzero
polynomials supply nontriviality; the native ring is an integral domain.\<close>

lemma natTrailingDegree_pow_of_ne_zero:
 fixes f::"'a::idom poly"
 assumes f: "f\<noteq>0"
 shows "order 0 (f^n)=n*order 0 f"
proof (induction n)
 case 0
 show ?case by simp
next
 case (Suc n)
 have product: "f^n*f\<noteq>0" using f by simp
 have "order 0 (f^Suc n)=order 0 (f^n)+order 0 f"
   by (simp only: power_Suc2 order_mult[OF product])
 then show ?case by (simp only: Suc.IH) (simp add: algebra_simps)
qed

lemma natTrailingDegree_X_pow_mul_of_coeff_zero_ne_zero:
 fixes g::"'a::idom poly"
 assumes constant_fact: "coeff g 0\<noteq>0"
 shows "order 0 ([:0,1:]^n*g)=n"
proof -
 have g: "g\<noteq>0" using constant_fact by auto
 have evaluated: "poly g 0\<noteq>0" using constant_fact by (simp only: poly_0_coeff_0; simp)
 have zero: "order 0 g=0" by (rule order_0I[OF evaluated])
 have product: "[:0,1:]^n*g\<noteq>0" using g by simp
 have Xorder: "order 0 ([:0,1:]^n)=n" using order_power_n_n[of 0 n] by simp
 show ?thesis by (simp only: order_mult[OF product] Xorder zero add_0)
qed

lemma power_ratio_lowest_order_divides:
 fixes f g::"'a::idom poly"
 assumes f: "f\<noteq>0" and c: "c\<noteq>0"
 and degree: "order 0 g=omega"
 and power: "f^rho=[:c:]*g"
 shows "rho dvd omega"
proof -
 have scalar: "[:c:]*g=smult c g" by simp
 have equality: "order 0 (f^rho)=order 0 ([:c:]*g)" by (rule arg_cong[OF power])
 have product: "rho*order 0 f=omega"
   using equality by (simp only: natTrailingDegree_pow_of_ne_zero[OF f]
     scalar order_smult[OF c] degree)
 show ?thesis by (rule dvdI[of _ _ "order 0 f"]) (rule sym[OF product])
qed

lemma cross_derivative_of_equal_powers:
 fixes F G::"complex bivariate"
 assumes positive: "0<n" and F: "F\<noteq>0"
 and power: "F^n=[:[:c:]:]*G^n"
 shows "G*biv_deriv is_y F=F*biv_deriv is_y G"
proof -
 obtain k where n: "n=Suc k" using positive by (cases n) auto
 let ?C="[:[:c:]:]::complex bivariate"
 have derivative_power: "biv_deriv is_y (T^Suc k)= of_nat(Suc k)*T^k*biv_deriv is_y T" for T
   by (cases is_y) (simp_all only: biv_deriv_def if_True if_False biv_dx_power_Suc biv_dy_power_Suc)
 have constant_fact: "biv_deriv is_y ?C=0"
   by (cases is_y) (simp_all add: biv_deriv_def biv_dx_def biv_dy_def map_poly_pCons)
 have derivative_mult: "biv_deriv is_y (A*B)=biv_deriv is_y A*B+A*biv_deriv is_y B" for A B
   by (cases is_y) (simp_all only: biv_deriv_def if_True if_False biv_dx_mult biv_dy_mult)
 have differentiated: "of_nat(Suc k)*F^k*biv_deriv is_y F=
   ?C*(of_nat(Suc k)*G^k*biv_deriv is_y G)"
   using arg_cong[OF power, of "biv_deriv is_y"]
   by (simp only: n derivative_power derivative_mult constant_fact mult_zero_left add_0)
 have Fpower: "F*F^k=F^Suc k" by (simp add: power_Suc mult.commute)
 have Gpower: "G*G^k=G^Suc k" by (simp add: power_Suc mult.commute)
 have factor: "(of_nat(Suc k)*F^k)*(G*biv_deriv is_y F-F*biv_deriv is_y G)=0"
 proof -
   have relation: "F^Suc k=?C*G^Suc k" using power by (simp only: n)
   have transported: "(of_nat(Suc k)*F^k*biv_deriv is_y F)*G=
     (?C*(of_nat(Suc k)*G^k*biv_deriv is_y G))*G"
     by (rule arg_cong[OF differentiated, where f="\<lambda>z. z*G"])
   have same: "(of_nat(Suc k)*F^k)*(G*biv_deriv is_y F)=
     (of_nat(Suc k)*F^k)*(F*biv_deriv is_y G)"
   proof -
     have "(of_nat(Suc k)*F^k)*(G*biv_deriv is_y F)=
       (of_nat(Suc k)*F^k*biv_deriv is_y F)*G" by algebra
     also have "...=(?C*(of_nat(Suc k)*G^k*biv_deriv is_y G))*G" by (rule transported)
     also have "...= of_nat(Suc k)*(?C*(G*G^k))*biv_deriv is_y G" by algebra
     also have "...= of_nat(Suc k)*(F*F^k)*biv_deriv is_y G"
       by (simp only: Gpower relation[symmetric] Fpower)
     also have "...=(of_nat(Suc k)*F^k)*(F*biv_deriv is_y G)" by algebra
     finally show ?thesis .
   qed
   show ?thesis by (simp only: right_diff_distrib same diff_self)
 qed
 have complex_cast: "(of_nat(Suc k)::complex)\<noteq>0"
   by (simp only: of_nat_eq_0_iff; simp)
 have scalar: "(of_nat(Suc k)::complex bivariate)\<noteq>0"
   using complex_cast by (simp only: of_nat_poly pCons_eq_0_iff; blast)
 have nonzero: "(of_nat(Suc k)::complex bivariate)*F^k\<noteq>0" using scalar F by simp
 have zero: "G*biv_deriv is_y F-F*biv_deriv is_y G=0"
   using factor nonzero by (simp only: mult_eq_0_iff; blast)
 show ?thesis by (rule iffD2[OF eq_iff_diff_eq_0 zero])
qed

lemma equal_positive_powers_scalar_ratio:
 fixes F G::"complex bivariate"
 assumes positive: "0<n" and F: "F\<noteq>0" and G: "G\<noteq>0"
 and power: "F^n=[:[:c:]:]*G^n"
 shows "\<exists>nu::complex. F=[:[:nu:]:]*G"
proof -
 have dx: "G*biv_dx F=F*biv_dx G"
   using cross_derivative_of_equal_powers[where is_y=False, OF positive F power]
   by (simp only: biv_deriv_def if_False)
 have dy: "G*biv_dy F=F*biv_dy G"
   using cross_derivative_of_equal_powers[where is_y=True, OF positive F power]
   by (simp only: biv_deriv_def if_True)
 show ?thesis by (rule bivariate_cross_derivatives_constant[OF G dx dy])
qed

end
