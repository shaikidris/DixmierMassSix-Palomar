theory Ramified_Corner_Parallel_Rigidity
 imports Ramified_Corner_Companion_Endpoints
begin

lemma ramified_corner_parallel_lattice_multiple:
 fixes l h j::nat and i::int
 assumes h: "0<h" and parallel: "i*int h=int j*(int l*int h-1)"
 shows "\<exists>mu::nat. j=mu*h \<and> i=int mu*(int l*int h-1)"
proof -
 have identity: "int j=int h*(int l*int j-i)" using parallel by (simp only: algebra_simps; linarith)
 have dividesZ: "int h dvd int j" unfolding dvd_def by (rule exI[of _ "int l*int j-i"]) (rule identity)
 have divides: "h dvd j" using dividesZ by (simp only: int_dvd_int_iff)
 obtain mu where shape: "j=h*mu" using divides by (auto simp: dvd_def)
 have cast: "int j=int h*int mu" by (simp only: shape of_nat_mult)
 have cross: "i*int h=(int mu*(int l*int h-1))*int h"
   using parallel by (simp only: cast; simp only: algebra_simps; linarith)
 have hnz: "int h\<noteq>0" using h by simp
 have first: "i=int mu*(int l*int h-1)" by (rule iffD1[OF mult_right_cancel[OF hnz] cross])
 show ?thesis by (intro exI[of _ mu]) (use shape first in auto)
qed

lemma ramified_corner_parallel_parameters:
 fixes l h mu j::nat and rho sigma i::int
 assumes l: "0<l" and h: "2\<le>h" and direction: "is_direction rho sigma" and rho: "0<rho"
 and balance: "int mu*(rho*(int l*int h-1)+int l*sigma*int h)=int l*(rho+sigma)"
 and point: "rho*i+int l*sigma*int j=rho*(int l*int h-1)+int l*sigma*int h"
 and grade: "0<i-int l*int j"
 shows "mu=1 \<and> h=2 \<and> rho=int l \<and> sigma=1-int l"
proof -
 let ?delta="rho+sigma"
 let ?w="rho*(int l*int h-1)+int l*sigma*int h"
 have delta: "0<?delta" using direction by (simp add: is_direction_def)
 have ld: "0<int l*?delta" using l delta by simp
 have mu: "0<mu"
 proof (rule ccontr)
   assume "\<not>0<mu"
   then have "mu=0" by arith
   then have "int l*?delta=0" using balance by simp
   then show False using ld by arith
 qed
 have grade1: "1\<le>i-int l*int j" using grade by arith
 have expression: "?w=rho*(i-int l*int j)+int l*?delta*int j" using point by (simp only: algebra_simps; linarith)
 have first: "rho\<le>rho*(i-int l*int j)"
 proof -
   have "rho*1\<le>rho*(i-int l*int j)" by (rule mult_left_mono[OF grade1]) (use rho in arith)
   then show ?thesis by simp
 qed
 have second: "0\<le>int l*?delta*int j" using ld by simp
 have lower: "rho\<le>?w" using first second by (simp only: expression; arith)
 have mubound: "int mu*rho\<le>int l*?delta"
 proof -
   have "int mu*rho\<le>int mu*?w" by (rule mult_left_mono[OF lower]) simp
   also have "...=int l*?delta" by (rule balance)
   finally show ?thesis .
 qed
 have relation: "int mu*rho=(int l*?delta)*(int mu*int h-1)" using balance by (simp only: algebra_simps; linarith)
 have productbound: "(int l*?delta)*(int mu*int h-1)\<le>(int l*?delta)*1"
   using mubound by (simp only: relation mult_1_right)
 have smallZ: "int mu*int h\<le>2"
   using iffD1[OF mult_le_cancel_left_pos[OF ld] productbound] by arith
 have small: "mu*h\<le>2"
 proof -
   have "int(mu*h)\<le>int(2::nat)" using smallZ by (simp only: of_nat_mult of_nat_numeral)
   then show ?thesis by (simp only: of_nat_le_iff)
 qed
 have muone: "mu=1"
 proof (rule ccontr)
   assume "mu\<noteq>1"
   then have two: "2\<le>mu" using mu by arith
   have "(2::nat)*2\<le>mu*h" by (rule mult_le_mono[OF two h])
   then show False using small by arith
 qed
 have htwo: "h=2" using small h by (simp only: muone mult_1_left; arith)
 have rdelta: "rho=int l*?delta" using relation by (simp only: muone htwo of_nat_numeral of_nat_1; simp only: algebra_simps; linarith)
 have sdelta: "sigma=?delta*(1-int l)" using rdelta by (simp only: algebra_simps; linarith)
 have rdvd: "?delta dvd rho"
   unfolding dvd_def by (rule exI[of _ "int l"]) (use rdelta in \<open>simp only: mult.commute\<close>)
 have sdvd: "?delta dvd sigma"
   unfolding dvd_def by (rule exI[of _ "1-int l"]) (rule sdelta)
 have castdelta: "int(nat ?delta)=?delta" using delta by simp
 have rnat: "nat ?delta dvd nat(abs rho)" using rdvd by (simp only: dvd_nat_abs_iff castdelta)
 have snat: "nat ?delta dvd nat(abs sigma)" using sdvd by (simp only: dvd_nat_abs_iff castdelta)
 have gcd: "gcd(nat(abs rho))(nat(abs sigma))=1" using direction by (simp add: is_direction_def)
 have one: "nat ?delta dvd (1::nat)" using gcd_greatest[OF rnat snat] by (simp only: gcd)
 have natone: "nat ?delta=1" using one by simp
 have deltaone: "?delta=1" using arg_cong[where f="int", OF natone] by (simp only: castdelta of_nat_1)
 have rho_value: "rho=int l" using rdelta by (simp only: deltaone mult_1_right)
 have sigma_value: "sigma=1-int l" using sdelta by (simp only: deltaone mult_1_left)
 show ?thesis by (intro conjI muone htwo rho_value sigma_value)
qed

lemma ramified_corner_parallel_endpoint_rigid:
 fixes l h jF j::nat and rho sigma iF i::int
 assumes l: "0<l" and h: "2\<le>h" and direction: "is_direction rho sigma" and rho: "0<rho"
 and parallel: "iF*int h=int jF*(int l*int h-1)"
 and Fweight: "rho*iF+int l*sigma*int jF=int l*(rho+sigma)"
 and point: "rho*i+int l*sigma*int j=rho*(int l*int h-1)+int l*sigma*int h"
 and grade: "0<i-int l*int j"
 shows "jF=2 \<and> iF=int l*2-1 \<and> h=2 \<and> rho=int l \<and> sigma=1-int l"
proof -
 have hpos: "0<h" using h by arith
 obtain mu where jf: "jF=mu*h" and ifirst: "iF=int mu*(int l*int h-1)"
   using ramified_corner_parallel_lattice_multiple[OF hpos parallel] by blast
 have balance: "int mu*(rho*(int l*int h-1)+int l*sigma*int h)=int l*(rho+sigma)"
   using Fweight by (simp only: jf ifirst of_nat_mult; simp only: algebra_simps; linarith)
 have parameters: "mu=1 \<and> h=2 \<and> rho=int l \<and> sigma=1-int l"
   by (rule ramified_corner_parallel_parameters[OF l h direction rho balance point grade])
 show ?thesis using parameters jf ifirst by auto
qed


lemma ramified_primitive_start_point_of_coprime_proportion:
 fixes l d n jP jQ::nat and iP iQ::int
 assumes d: "0<d" and cop: "coprime d n"
 and first: "int n*iP=int d*iQ" and second: "n*jP=d*jQ"
 and grade: "-int d<iP-int l*int jP" and nondiag: "iP-int l*int jP\<noteq>0"
 shows "\<exists>i::int. \<exists>j::nat. iP=int d*i \<and> jP=d*j \<and> 0<i-int l*int j"
proof -
 have copZ: "coprime(int d)(int n)" using cop by (simp only: coprime_int_iff)
 have firstdiv: "int d dvd int n*iP" by (simp only: first) simp
 have seconddiv: "d dvd n*jP" by (simp only: second) simp
 have firstdiv_commuted: "int d dvd iP*int n" using firstdiv by (simp only: mult.commute)
 have di: "int d dvd iP" by (rule iffD1[OF coprime_dvd_mult_left_iff[OF copZ] firstdiv_commuted])
 have seconddiv_commuted: "d dvd jP*n" using seconddiv by (simp only: mult.commute)
 have dj: "d dvd jP" by (rule iffD1[OF coprime_dvd_mult_left_iff[OF cop] seconddiv_commuted])
 obtain i where firstshape: "iP=int d*i" using di by (auto simp: dvd_def)
 obtain j where secondshape: "jP=d*j" using dj by (auto simp: dvd_def)
 have shape: "iP-int l*int jP=int d*(i-int l*int j)"
   by (simp only: firstshape secondshape of_nat_mult; algebra)
 have dZ: "0<int d" using d by simp
 have productbound: "int d*(-1)<int d*(i-int l*int j)" using grade by (simp only: shape mult_minus_right mult_1_right)
 have bound: "-1<i-int l*int j" by (rule iffD1[OF mult_less_cancel_left_pos[OF dZ] productbound])
 have nonzero: "i-int l*int j\<noteq>0" using nondiag by (simp only: shape mult_eq_0_iff; blast)
 have positive: "0<i-int l*int j" using bound nonzero by arith
 show ?thesis by (intro exI[of _ i] exI[of _ j]) (use firstshape secondshape positive in auto)
qed

end
