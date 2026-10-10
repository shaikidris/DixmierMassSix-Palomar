theory Crossing_Cut_Consumer
 imports "Crossing_Face_Cut_Root"
begin

lemma crossingPair_ending_grades_negative:
 fixes P Q::"complex poly_operator" and p q j rho s::nat
 assumes alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and nu: "nu\<noteq>0"
 and p: "0<p" and q: "2\<le>q" and j: "0<j" and s: "0<s"
 and parameter: "(q-1)*rho=q*s+1"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and Qf: "leading_form (int rho) (-int s) Q=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
 shows "(\<exists>u\<in>biv_support(leading_form (int rho) (-int s) P). pair_grade u<0) \<and>
 (\<exists>u\<in>biv_support(leading_form (int rho) (-int s) Q). pair_grade u<0)"
proof -
 have rho: "0<rho" by (rule purePower_rho_pos[OF q parameter])
 have P: "(p+s*(q*p),rho*q*p)\<in>biv_support(leading_form (int rho) (-int s) P)"
   "pair_grade(p+s*(q*p),rho*q*p)=-(int p*int rho)"
   using crossingFace_ending_endpoint[OF alpha mu q s p parameter Pf] by blast+
 have Q: "(j+s*(q*j),rho*q*j)\<in>biv_support(leading_form (int rho) (-int s) Q)"
   "pair_grade(j+s*(q*j),rho*q*j)=-(int j*int rho)"
   using crossingFace_ending_endpoint[OF alpha nu q s j parameter Qf] by blast+
 have Ppositive: "0<int p*int rho" by (rule mult_pos_pos) (use p rho in simp_all)
 have Qpositive: "0<int j*int rho" by (rule mult_pos_pos) (use j rho in simp_all)
 have Pnegative: "pair_grade(p+s*(q*p),rho*q*p)<0" using P(2) Ppositive by arith
 have Qnegative: "pair_grade(j+s*(q*j),rho*q*j)<0" using Q(2) Qpositive by arith
 have Pexists: "\<exists>u\<in>biv_support(leading_form (int rho) (-int s) P). pair_grade u<0"
   by (rule bexI[where x="(p+s*(q*p),rho*q*p)"], rule Pnegative, rule P(1))
 have Qexists: "\<exists>u\<in>biv_support(leading_form (int rho) (-int s) Q). pair_grade u<0"
   by (rule bexI[where x="(j+s*(q*j),rho*q*j)"], rule Qnegative, rule Q(1))
 show ?thesis by (rule conjI[OF Pexists Qexists])
qed

lemma crossingPair_cutCorner_contradiction:
 fixes P Q::"complex poly_operator" and p q j rho s::nat
 assumes H: "GGVInputs" and alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and nu: "nu\<noteq>0"
 and p: "prime p" and q: "2\<le>q" and j: "1<j" and s: "0<s"
 and parameter: "(q-1)*rho=q*s+1" and cop: "coprime j p"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Qw: "v_degree (int rho) (-int s) Q=int(rho*j)"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and Qf: "leading_form (int rho) (-int s) Q=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
 and pair: "is_counterexample_pair P Q"
 shows False
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" using pair by (simp_all add: is_counterexample_pair_def)
 have rho: "0<rho" by (rule purePower_rho_pos[OF q parameter])
 have sr: "s<rho" by (rule purePower_s_lt_rho[OF q parameter])
 have dir: "is_direction (int rho) (-int s)" by (rule purePower_isDirection[OF q parameter])
 have p2: "2\<le>p" by (rule prime_ge_2_nat[OF p])
 have pp: "0<p" using p2 by arith
 have jp: "0<j" using j by arith
 have qp: "0<q" using q by arith
 have Ppos: "0<v_degree (int rho) (-int s) P" using pp rho by (simp only: Pw; simp)
 have Qpos: "0<v_degree (int rho) (-int s) Q" using jp rho by (simp only: Qw; simp)
 have Pge: "2*int rho\<le>int p*int rho" by (rule mult_right_mono) (use p2 in simp_all)
 have Qge: "2*int rho\<le>int j*int rho" by (rule mult_right_mono) (use j in simp_all)
 have small: "int rho+(-int s)<v_degree (int rho) (-int s) P+v_degree (int rho) (-int s) Q"
   using Pge Qge rho by (simp only: Pw Qw of_nat_mult; simp only: mult.commute; arith)
 have ratio: "\<not>v_degree (int rho) (-int s) P dvd v_degree (int rho) (-int s) Q"
   "\<not>v_degree (int rho) (-int s) Q dvd v_degree (int rho) (-int s) P"
   "v_degree (int rho) (-int s) Q*int p=v_degree (int rho) (-int s) P*int j"
   using primeMate_terminal_signed_ratio[OF P Q p j rho cop Pw Qw] by blast+
 have common: "in_direction (int rho) (-int s) P" "in_direction (int rho) (-int s) Q"
   using crossingPair_commonDirection[OF alpha mu nu pp qp jp s Pf Qf] by blast+
 have negatives: "\<exists>u\<in>biv_support(leading_form (int rho) (-int s) P). pair_grade u<0"
   "\<exists>u\<in>biv_support(leading_form (int rho) (-int s) Q). pair_grade u<0"
   using crossingPair_ending_grades_negative[OF alpha mu nu pp q jp s parameter Pf Qf] by blast+
 have start: "(p,0)\<in>biv_support(leading_form (int rho) (-int s) P)"
   "\<forall>u\<in>biv_support(leading_form (int rho) (-int s) P). pair_grade u\<le>pair_grade(p,0)"
   using crossingFace_starting_point[OF P mu s sr pp Pf] by blast+
 have root: "max_root_mult(cut_poly (int rho) (-int s) P)=q*p"
   by (rule crossingFace_cutPoly_maxRootMult[OF alpha mu qp rho pp Pf])
 have corner: "GGVCutCornerInput" by (rule GGVInputs_cutCorner[OF H])
 note chosen = corner[unfolded GGVCutCornerInput_def,
   THEN spec[where x=P], THEN spec[where x=Q],
   THEN spec[where x="int rho"], THEN spec[where x="-int s"],
   THEN spec[where x=p], THEN spec[where x="0::nat"],
   THEN spec[where x=j], THEN spec[where x=p], THEN spec[where x=q]]
 have rho_positive: "0<int rho" using rho by simp
 have sigma_nonpositive: "-int s\<le>0" by simp
 have p_gt_one: "1<p" using p2 by arith
 note applied = chosen[THEN mp, OF pair, THEN mp, OF dir,
   THEN mp, OF rho_positive, THEN mp, OF sigma_nonpositive,
   THEN mp, OF common(1), THEN mp, OF common(2),
   THEN mp, OF Ppos, THEN mp, OF Qpos, THEN mp, OF small,
   THEN mp, OF ratio(1), THEN mp, OF ratio(2),
   THEN mp, OF negatives(1), THEN mp, OF negatives(2),
   THEN mp, OF start(1), THEN mp, OF start(2), THEN mp, OF ratio(3),
   THEN mp, OF j, THEN mp, OF p_gt_one, THEN mp, OF cop, THEN mp, OF q]
 have forbidden: "\<not>(((of_nat p+((0::rat)- of_nat(max_root_mult(cut_poly (int rho) (-int s) P)))* of_int(-int s)/ of_int(int rho))/ of_nat p=
 of_nat q-1/ of_int(int rho)) \<and> (of_nat(max_root_mult(cut_poly (int rho) (-int s) P))::rat)/ of_nat p= of_nat q)"
   using applied by (simp only: of_nat_0 not_False_eq_True)
 have pnz: "(of_nat p::rat)\<noteq>0" using pp by simp
 have rnz: "(of_nat rho::rat)\<noteq>0" using rho by simp
 have normalized: "(1::rat)+ of_nat q* of_nat s/ of_nat rho= of_nat q-1/ of_nat rho"
   by (rule purePower_normalized_corner[OF q parameter])
 have first: "((of_nat p+((0::rat)- of_nat(q*p))* of_int(-int s)/ of_int(int rho))/ of_nat p)= of_nat q-1/ of_int(int rho)"
 proof -
   have numerator: "(of_nat p::rat)+(of_nat q* of_nat p)* of_nat s/ of_nat rho=
     of_nat p*(1+ of_nat q* of_nat s/ of_nat rho)"
     by (simp only: divide_inverse distrib_left mult_1_right mult_1_left mult.assoc mult.left_commute mult.commute)
   have cancellation: "(of_nat p*(1+ of_nat q* of_nat s/ of_nat rho)::rat)/ of_nat p=
     1+ of_nat q* of_nat s/ of_nat rho"
     by (simp only: times_divide_eq_left[symmetric] divide_self[OF pnz] mult_1_left)
   have reform: "((of_nat p+((0::rat)- of_nat(q*p))* of_int(-int s)/ of_int(int rho))/ of_nat p)=1+ of_nat q* of_nat s/ of_nat rho"
     by (simp only: of_nat_mult of_int_minus of_int_of_nat_eq diff_0 minus_mult_minus numerator cancellation)
   show ?thesis using trans[OF reform normalized] by (simp only: of_int_of_nat_eq)
 qed
 have second: "(of_nat(q*p)::rat)/ of_nat p= of_nat q" using pnz by (simp add: of_nat_mult)
 show False using forbidden first second by (simp only: root; blast)
qed

lemma crossingFace_strict_exclusion:
 fixes P Q::"complex poly_operator" and p q rho s::nat
 assumes H: "GGVInputs" and alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and p: "prime p"
 and q: "2\<le>q" and s: "0<s" and parameter: "(q-1)*rho=q*s+1"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and pair: "is_counterexample_pair P Q"
 shows False
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have rho: "0<rho" by (rule purePower_rho_pos[OF q parameter])
 have sr: "s<rho" by (rule purePower_s_lt_rho[OF q parameter])
 have dir: "is_direction (int rho) (-int s)" by (rule purePower_isDirection[OF q parameter])
 have pp: "0<p" using prime_ge_2_nat[OF p] by arith
 have start: "(p,0)\<in>biv_support(leading_form (int rho) (-int s) P)"
   by (rule crossing_power_starting_support[OF mu rho Pf])
 have Pw: "v_degree (int rho) (-int s) P=int p*int rho"
   using weight_of_mem_leadingForm[OF P start] by (simp add: pair_weight_def mult.commute)
 obtain Q' j nu where pair': "is_counterexample_pair P Q'" and j: "1<j" and cop: "coprime j p" and nu: "nu\<noteq>0"
 and Qw: "v_degree (int rho) (-int s) Q'=int(rho*j)"
 and Qf: "leading_form (int rho) (-int s) Q'=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
   using crossingFace_prime_terminal[OF H mu p s sr dir Pw Pf pair] by blast
 show False by (rule crossingPair_cutCorner_contradiction[OF H alpha mu nu p q j s parameter cop Pw Qw Pf Qf pair'])
qed

end
