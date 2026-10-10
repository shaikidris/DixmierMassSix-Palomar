theory Small_Degree_Direction_Arithmetic
 imports "Small_Degree_Coordinate_Tables"
begin

lemma gcd_normalized_direction_companion_weight:
 fixes f1 f2 :: nat
 assumes first: "0<f1" and second: "0<f2"
 shows "let d=gcd (f1-1) (f2-1); rho=(f2-1) div d; k=(f1-1) div d
   in rho*f1+k=k*f2+rho"
proof -
 let ?d = "gcd (f1-1) (f2-1)"
 let ?rho = "(f2-1) div ?d"
 let ?k = "(f1-1) div ?d"
 have a: "?k*?d=f1-1" by (rule dvd_div_mult_self[OF gcd_dvd1])
 have b: "?rho*?d=f2-1" by (rule dvd_div_mult_self[OF gcd_dvd2])
 have cross: "?rho*(f1-1)=?k*(f2-1)"
 proof -
   have "?rho*(f1-1)=?rho*(?k*?d)" by (rule arg_cong[OF a[symmetric]])
   also have "...=?k*(?rho*?d)" by (simp only: mult.assoc mult.left_commute mult.commute)
   also have "...=?k*(f2-1)" by (simp only: b)
   finally show ?thesis .
 qed
 have f1_eq: "f1=(f1-1)+1" using first by arith
 have f2_eq: "f2=(f2-1)+1" using second by arith
 have expand_first: "?rho*f1=?rho*(f1-1)+?rho"
 proof -
   have "?rho*f1=?rho*((f1-1)+1)" by (rule arg_cong[OF f1_eq])
   then show ?thesis by (simp add: algebra_simps)
 qed
 have expand_second: "?k*f2=?k*(f2-1)+?k"
 proof -
   have "?k*f2=?k*((f2-1)+1)" by (rule arg_cong[OF f2_eq])
   then show ?thesis by (simp add: algebra_simps)
 qed
 show ?thesis by (simp only: Let_def expand_first expand_second cross; arith)
qed

lemma gcd_normalized_direction_strict:
 fixes u v f1 f2 :: nat
 assumes main: "u<v" and first: "2\<le>f1"
   and proportional: "f1*v=f2*u"
 shows "let d=gcd (f1-1) (f2-1)
   in 0<(f1-1) div d \<and> (f1-1) div d<(f2-1) div d"
proof -
 have f1_positive: "0<f1" using first by arith
 have f2_greater: "f1<f2"
 proof (rule ccontr)
   assume "\<not>f1<f2"
   then have le: "f2\<le>f1" by arith
   have strict: "f1*u<f1*v" using main f1_positive by simp
   have bound: "f2*u\<le>f1*u" by (rule mult_right_mono[OF le]) simp
   show False using strict bound proportional by arith
 qed
 let ?d = "gcd (f1-1) (f2-1)"
 let ?k = "(f1-1) div ?d"
 let ?rho = "(f2-1) div ?d"
 have first_difference_nonzero: "f1-1\<noteq>0" using first by arith
 have d_positive: "0<?d" using first_difference_nonzero by simp
 have a: "?k*?d=f1-1" by (rule dvd_div_mult_self[OF gcd_dvd1])
 have b: "?rho*?d=f2-1" by (rule dvd_div_mult_self[OF gcd_dvd2])
 have first_positive: "0<f1-1" using first by arith
 have k_positive: "0<?k"
 proof (rule ccontr)
   assume "\<not>0<?k"
   then have k_zero: "?k=0" by arith
   have "f1-1=0" using a by (simp only: k_zero mult_zero_left)
   then show False using first_positive by arith
 qed
 have difference: "f1-1<f2-1" using f2_greater first by arith
 have product_strict: "?k*?d<?rho*?d" by (simp only: a b; rule difference)
 have strict: "?k<?rho" using product_strict
   by (simp only: mult_less_cancel2; blast)
 show ?thesis by (simp only: Let_def; intro conjI k_positive strict)
qed

end
