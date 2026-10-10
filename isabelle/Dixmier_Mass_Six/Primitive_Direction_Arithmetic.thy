theory Primitive_Direction_Arithmetic
 imports "HOL-Computational_Algebra.Polynomial"
begin
lemma primitive_direction_of_weight_line:
 fixes rho s a b :: nat
 assumes rp: "0<rho" and ap: "0<a" and cop: "coprime rho s"
   and line: "rho*a=s*b"
 shows "rho=b div gcd a b \<and> s=a div gcd a b"
proof -
 have dvd: "rho dvd b*s" using line by (metis dvd_triv_left mult.commute)
 have rb: "rho dvd b" using dvd by (simp only: coprime_dvd_mult_left_iff[OF cop])
 define k where "k=b div rho"
 have b: "b=rho*k" using rb by (simp add: k_def)
 have kp: "0<k"
 proof (rule ccontr)
  assume "\<not>0<k"
  then have "k=0" by simp
  then have "rho*a=0" using line b by simp
  with rp ap show False by simp
 qed
 have eq: "rho*a=rho*(s*k)" using line b by (simp add: algebra_simps)
 have a: "a=s*k" using eq rp by simp
 have g: "gcd a b=k" using cop by (simp add: a b gcd_mult_right gcd.commute)
 show ?thesis unfolding g using kp by (simp add: a b)
qed
lemma nonprimitive_control:
 "(4::nat)*3=6*2 \<and> (4::nat)\<noteq>2 div gcd 3 2"
 by simp
lemma zero_vector_control:
 "(2::nat)*0=3*0 \<and> (2::nat)\<noteq>0 div gcd 0 0"
 by simp
end
