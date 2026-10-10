theory Small_Degree_Companion_Properness
 imports Small_Degree_Direction_Arithmetic
begin

lemma companion_endpoint_proper_of_weight:
 fixes rho sigma u v r t f1 f2 :: int
 assumes rho: "0<rho" and sigma: "sigma<0" and sum: "0<rho+sigma"
   and u: "0<u" and t: "0\<le>t" and crossing: "t<r"
   and line: "rho*u+sigma*v=rho*r+sigma*t"
   and companion: "rho*f1+sigma*f2=rho+sigma"
   and proportional: "f1*v=f2*u"
 shows "f1<u"
proof -
 have gap: "1\<le>r-t" using crossing by arith
 have first: "rho\<le>rho*(r-t)" using mult_left_mono[OF gap, of rho] rho by simp
 have rest: "0\<le>(rho+sigma)*t" by (rule mult_nonneg_nonneg) (use sum t in auto)
 have expanded: "rho*r+sigma*t=rho*(r-t)+(rho+sigma)*t"
   by (simp add: algebra_simps)
 have weight_above: "rho+sigma<rho*u+sigma*v"
   using first rest sigma by (simp only: line expanded; arith)
 have cross: "u*f2=f1*v" using proportional by (simp only: mult.commute)
 have identity: "u*(rho+sigma)=f1*(rho*u+sigma*v)"
 proof -
   have "u*(rho+sigma)=u*(rho*f1+sigma*f2)" by (rule arg_cong[OF companion[symmetric]])
   also have "...=rho*(u*f1)+sigma*(u*f2)" by (simp add: algebra_simps)
   also have "...=rho*(u*f1)+sigma*(f1*v)" by (rule arg_cong[OF cross])
   also have "...=f1*(rho*u+sigma*v)" by (simp add: algebra_simps)
   finally show ?thesis .
 qed
 show ?thesis
 proof (rule ccontr)
   assume "\<not>f1<u"
   then have larger: "u\<le>f1" by arith
   have positive_weight: "0<rho*u+sigma*v" using weight_above sum by arith
   have strict: "u*(rho+sigma)<u*(rho*u+sigma*v)"
     by (rule mult_strict_left_mono[OF weight_above u])
   have weak: "u*(rho*u+sigma*v)\<le>f1*(rho*u+sigma*v)"
     by (rule mult_right_mono[OF larger]) (use positive_weight in auto)
   show False using identity strict weak by arith
 qed
qed

lemma companion_endpoint_both_proper_of_weight:
 fixes rho sigma u v r t f1 f2 :: int
 assumes rho: "0<rho" and sigma: "sigma<0" and sum: "0<rho+sigma"
   and u: "0<u" and v: "0<v" and t: "0\<le>t" and crossing: "t<r"
   and line: "rho*u+sigma*v=rho*r+sigma*t"
   and companion: "rho*f1+sigma*f2=rho+sigma"
   and proportional: "f1*v=f2*u"
 shows "f1<u\<and>f2<v"
proof -
 have first: "f1<u"
   by (rule companion_endpoint_proper_of_weight[OF rho sigma sum u t crossing line companion proportional])
 have second: "f2<v"
 proof (rule ccontr)
   assume "\<not>f2<v"
   then have larger: "v\<le>f2" by arith
   have strict: "f1*v<u*v" by (rule mult_strict_right_mono[OF first v])
   have weak: "u*v\<le>u*f2" by (rule mult_left_mono[OF larger]) (use u in auto)
   show False using strict weak proportional by (simp only: mult.commute; arith)
 qed
 show ?thesis using first second by blast
qed

lemma companion_endpoint_both_proper_nat:
 fixes rho k u v r s f1 f2 :: nat
 assumes k: "0<k" and direction: "k<rho" and u: "0<u" and v: "0<v"
   and crossing: "s<r"
   and line: "rho*u+k*s=rho*r+k*v"
   and companion: "rho*f1+k=k*f2+rho"
   and proportional: "f1*v=f2*u"
 shows "f1<u\<and>f2<v"
proof -
 have rhoZ: "0<int rho" using k direction by arith
 have sigmaZ: "-int k<0" using k by simp
 have sumZ: "0<int rho-int k" using direction by simp
 have uZ: "0<int u" using u by simp
 have vZ: "0<int v" using v by simp
 have crossingZ: "int s<int r" using crossing by simp
 have line_cast: "int rho*int u+int k*int s=int rho*int r+int k*int v"
   using arg_cong[OF line, of int] by (simp only: of_nat_add of_nat_mult)
 have lineZ: "int rho*int u+(-int k)*int v=int rho*int r+(-int k)*int s"
   using line_cast by (simp only: mult_minus_left; arith)
 have companion_cast: "int rho*int f1+int k=int k*int f2+int rho"
   using arg_cong[OF companion, of int] by (simp only: of_nat_add of_nat_mult)
 have companionZ: "int rho*int f1+(-int k)*int f2=int rho+(-int k)"
   using companion_cast by (simp only: mult_minus_left; arith)
 have proportionalZ: "int f1*int v=int f2*int u"
   using arg_cong[OF proportional, of int] by (simp only: of_nat_mult)
 have proper: "int f1<int u\<and>int f2<int v"
   by (rule companion_endpoint_both_proper_of_weight[OF rhoZ sigmaZ _ uZ vZ _ crossingZ
      lineZ companionZ proportionalZ]) (use sumZ in auto)
 show ?thesis using proper by simp
qed

end
