theory Companion_Endpoint_Properness
 imports Companion_Nonmonomial "HOL.GCD"
begin

lemma companion_endpoint_proper_of_weight:
 fixes rho sigma u v r t f1 f2::int
 assumes rho: "0<rho" and sigma: "sigma<0" and sum: "0<rho+sigma"
 and u: "0<u" and t: "0\<le>t" and start: "t<r"
 and line: "rho*u+sigma*v=rho*r+sigma*t"
 and companion: "rho*f1+sigma*f2=rho+sigma"
 and proportional: "f1*v=f2*u"
 shows "f1<u"
proof -
 let ?q="rho*r+sigma*t"
 have gap: "1\<le>r-t" using start by arith
 have product: "rho\<le>rho*(r-t)"
   using mult_left_mono[OF gap, of rho] rho by simp
 have remainder: "0\<le>(rho+sigma)*t" by (rule mult_nonneg_nonneg) (use sum t in auto)
 have weight: "rho+sigma<?q"
   using product remainder sigma by (simp add: algebra_simps; arith)
 have q: "0<?q" using weight sum by arith
 have cross: "u*(rho+sigma)=f1*(rho*u+sigma*v)"
 proof -
   have expanded: "u*(rho*f1+sigma*f2)=f1*(rho*u+sigma*v)"
     using arg_cong[OF proportional, of "\<lambda>z. sigma*z"] by algebra
   show ?thesis using expanded companion by simp
 qed
 show ?thesis
 proof (rule ccontr)
   assume "\<not>f1<u"
   then have le: "u\<le>f1" by arith
   have smaller: "u*(rho+sigma)<u*?q"
     by (rule mult_strict_left_mono[OF weight u])
   have bigger: "u*?q\<le>f1*?q"
     by (rule mult_right_mono[OF le]) (use q in simp)
   show False using cross line smaller bigger by arith
 qed
qed

lemma companion_endpoint_both_proper_of_weight:
 fixes rho sigma u v r t f1 f2::int
 assumes rho: "0<rho" and sigma: "sigma<0" and sum: "0<rho+sigma"
 and u: "0<u" and v: "0<v" and t: "0\<le>t" and start: "t<r"
 and line: "rho*u+sigma*v=rho*r+sigma*t"
 and companion: "rho*f1+sigma*f2=rho+sigma"
 and proportional: "f1*v=f2*u"
 shows "f1<u \<and> f2<v"
proof -
 have first: "f1<u" by (rule companion_endpoint_proper_of_weight[OF rho sigma sum u t start line companion proportional])
 have second: "f2<v"
 proof (rule ccontr)
   assume "\<not>f2<v"
   then have le: "v\<le>f2" by arith
   have smaller: "f1*v<u*v" by (rule mult_strict_right_mono[OF first v])
   have larger: "v*u\<le>f2*u" by (rule mult_right_mono[OF le]) (use u in simp)
   show False using smaller larger proportional by (simp add: mult.commute; arith)
 qed
 show ?thesis using first second by blast
qed

lemma companion_endpoint_both_proper_nat:
 fixes rho k u v r s f1 f2::nat
 assumes k: "0<k" and direction: "k<rho" and u: "0<u" and v: "0<v" and start: "s<r"
 and line: "rho*u+k*s=rho*r+k*v"
 and companion: "rho*f1+k=k*f2+rho"
 and proportional: "f1*v=f2*u"
 shows "f1<u \<and> f2<v"
proof -
 have rho: "0<int rho" using k direction by simp
 have sigma: "-int k<0" using k by simp
 have sum: "0<int rho+(-int k)" using direction by simp
 have uc: "0<int u" using u by simp
 have vc: "0<int v" using v by simp
 have tc: "0\<le>int s" by simp
 have rc: "int s<int r" using start by simp
 have lc: "int rho*int u+(-int k)*int v=int rho*int r+(-int k)*int s"
   using arg_cong[OF line, of int] by (simp only: of_nat_add of_nat_mult; arith)
 have cc: "int rho*int f1+(-int k)*int f2=int rho+(-int k)"
   using arg_cong[OF companion, of int] by (simp only: of_nat_add of_nat_mult; arith)
 have pc: "int f1*int v=int f2*int u" using arg_cong[OF proportional, of int] by (simp only: of_nat_mult)
 have result: "int f1<int u \<and> int f2<int v"
   by (rule companion_endpoint_both_proper_of_weight[OF rho sigma sum uc vc tc rc lc cc pc])
 show ?thesis using result by simp
qed

lemma proportional_lattice_point_not_coprime:
 fixes u v f1 f2::nat
 assumes positive: "0<f1" and proper: "f1<u" and proportional: "f1*v=f2*u"
 shows "\<not>coprime u v"
proof
 assume coprime: "coprime u v"
 have divides: "u dvd f1*v" using proportional by (metis dvd_triv_right)
 have f: "u dvd f1" using divides by (simp only: coprime_dvd_mult_left_iff[OF coprime])
 have "u\<le>f1" by (rule dvd_imp_le[OF f positive])
 then show False using proper by arith
qed

lemma proportional_lattice_point_gcd_gt_one:
 fixes u v f1 f2::nat
 assumes positive: "0<f1" and proper: "f1<u" and proportional: "f1*v=f2*u"
 shows "1<gcd u v"
proof -
 have u: "0<u" using positive proper by arith
 have gcd: "0<gcd u v" using u by simp
 have noncoprime: "\<not>coprime u v" by (rule proportional_lattice_point_not_coprime[OF positive proper proportional])
 show ?thesis using gcd noncoprime by (simp add: coprime_iff_gcd_eq_1; arith)
qed
end
