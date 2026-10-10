theory Pure_Power_Arithmetic
 imports "Weighted_Newton_Definitions"
   "HOL-Computational_Algebra.Primes"
begin

lemma purePower_rho_pos:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "0<rho"
 using equation by (cases rho) auto

lemma purePower_s_lt_rho:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "s<rho"
proof -
 have q1: "q-1+1=q" using q by arith
 have split: "q*rho=(q-1)*rho+rho"
  using arg_cong[OF q1, where f="\<lambda>x. x*rho"] by (simp add: distrib_right)
 show ?thesis
 proof (rule ccontr)
  assume "\<not>s<rho"
  then have "rho\<le>s" by arith
  then have product: "q*rho\<le>q*s" by (rule mult_le_mono2)
  show False using split equation product by arith
 qed
qed

lemma purePower_horizontal_parameters:
 fixes q rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*0+1"
 shows "q=2 \<and> rho=1"
proof -
 have one: "(q-1)*rho=1" using equation by simp
 have d1: "q-1 dvd 1" using one by (metis dvd_triv_left)
 have d2: "rho dvd 1" using one by (metis dvd_triv_right)
 have "q-1=1" and "rho=1" using d1 d2 by simp_all
 then show ?thesis using q by arith
qed

lemma purePower_coprime:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "coprime rho s"
proof -
 let ?g="gcd rho s"
 have left: "?g dvd (q-1)*rho" by (rule dvd_mult) simp
 have right: "?g dvd q*s" by (rule dvd_mult) simp
 have total_divides: "?g dvd q*s+1" using left by (simp only: equation)
 have unit_divides: "?g dvd 1"
   by (rule iffD1[OF dvd_add_right_iff[OF right] total_divides])
 show ?thesis using unit_divides by (simp add: coprime_iff_gcd_eq_1)
qed

lemma purePower_isDirection:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "is_direction(int rho)(-int s)"
 using purePower_coprime[OF q equation] purePower_s_lt_rho[OF q equation]
 by (simp add: is_direction_def coprime_iff_gcd_eq_1)

lemma purePower_weight_identity:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "int q*(int rho-int s)=int rho+1"
proof -
 have signed: "(int q-1)*int rho=int q*int s+1"
  using arg_cong[OF equation, where f=int] q by (simp add: of_nat_diff)
 show ?thesis using signed by (simp add: algebra_simps; arith)
qed

lemma purePower_normalized_corner:
 fixes q s rho::nat
 assumes q: "2\<le>q" and equation: "(q-1)*rho=q*s+1"
 shows "(1::rat)+ of_nat q* of_nat s/ of_nat rho= of_nat q-1/ of_nat rho"
proof -
 have rho: "0<rho" by (rule purePower_rho_pos[OF q equation])
 have signed: "((of_nat q::rat)-1)* of_nat rho= of_nat q* of_nat s+1"
  using arg_cong[OF equation, where f="\<lambda>x::nat. of_nat x::rat"] q by (simp add: of_nat_diff)
 have rnz: "(of_nat rho::rat)\<noteq>0" using rho by simp
 have total: "(of_nat rho::rat)+ of_nat q* of_nat s= of_nat q* of_nat rho-1"
   using signed by (simp add: algebra_simps; linarith)
 show ?thesis by (simp only: add_divide_eq_iff[OF rnz] diff_divide_eq_iff[OF rnz] mult_1_left total)
qed

lemma primeMateExponent_coprime:
 fixes p j::nat
 assumes p: "prime p" and nondividing: "\<not>p dvd j"
 shows "coprime j p"
 using prime_imp_coprime[OF p nondividing] by (simp add: coprime_commute)

lemma pure_power_common_weight_divisibility:
 fixes a b rho::nat
 assumes rho: "0<rho"
 shows "a*rho dvd b*rho \<longleftrightarrow> a dvd b"
proof
 assume "a*rho dvd b*rho"
 then obtain k where "b*rho=(a*rho)*k" by (elim dvdE)
 then have "b*rho=(a*k)*rho" by (simp add: mult_ac)
 then have "b=a*k" using rho by simp
 then show "a dvd b" by (auto simp: dvd_def)
next
 assume "a dvd b"
 then show "a*rho dvd b*rho" by (rule mult_dvd_mono) simp
qed

lemma primeMateWeights_nonintegral:
 fixes p j rho::nat
 assumes p: "prime p" and j: "1<j" and rho: "0<rho" and nondividing: "\<not>p dvd j"
 shows "\<not>p*rho dvd j*rho \<and> \<not>j*rho dvd p*rho"
proof (intro conjI notI)
 assume "p*rho dvd j*rho"
 then have "p dvd j" by (simp only: pure_power_common_weight_divisibility[OF rho])
 then show False using nondividing by contradiction
next
 assume "j*rho dvd p*rho"
 then have divides: "j dvd p" by (simp only: pure_power_common_weight_divisibility[OF rho])
 have alternatives: "j=1 \<or> j=p" using p divides by (auto simp: prime_nat_iff)
 have "j=p" using alternatives j by arith
 then show False using nondividing by simp
qed

lemma primeMateWeight_ratio:
 fixes p j rho::nat
 assumes p: "prime p" and rho: "0<rho"
 shows "(of_nat(j*rho)::rat)/ of_nat(p*rho)= of_nat j/ of_nat p"
proof -
 have ppos: "0<p" by (rule prime_gt_0_nat[OF p])
 have rnz: "(of_nat rho::rat)\<noteq>0" using rho by simp
 show ?thesis by (simp only: of_nat_mult nonzero_mult_divide_mult_cancel_right[OF rnz])
qed

lemma primeMateWeights_nonintegral_int:
 fixes p j rho::nat
 assumes p: "prime p" and j: "1<j" and rho: "0<rho" and nondividing: "\<not>p dvd j"
 shows "\<not>int p*int rho dvd int j*int rho \<and> \<not>int j*int rho dvd int p*int rho"
 using primeMateWeights_nonintegral[OF p j rho nondividing]
 by (simp only: of_nat_mult[symmetric] int_dvd_int_iff; simp)

end
