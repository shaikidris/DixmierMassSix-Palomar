theory Horizontal_Corner_Exclusion
 imports "Crossing_Face_Endpoints"
begin

lemma horizontalPair_corner_contradiction:
 fixes P Q::"complex poly_operator" and p j::nat
 assumes H: "GGVInputs" and alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and nu: "nu\<noteq>0"
 and p: "prime p" and j: "1<j" and cop: "coprime j p"
 and Pf: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
 and Qw: "v_degree 1 0 Q=int j"
 and Qf: "leading_form 1 0 Q=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
 and pair: "is_counterexample_pair P Q"
 shows False
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" using pair by (simp_all add: is_counterexample_pair_def)
 have Pw: "v_degree 1 0 P=int p" by (rule horizontalFace_weight[OF P mu Pf])
 have p2: "2\<le>p" by (rule prime_ge_2_nat[OF p])
 have pp: "0<p" using p2 by arith
 have jp: "0<j" using j by arith
 have dir: "is_direction (1::int) 0" by (simp add: is_direction_def)
 have common: "in_direction 1 0 P" "in_direction 1 0 Q"
   using horizontalFace_support_two[OF alpha mu pp Pf] horizontalFace_support_two[OF alpha nu jp Qf]
   by (simp_all only: in_direction_def)
 have Ppos: "0<v_degree 1 0 P" using pp by (simp only: Pw; simp)
 have Qpos: "0<v_degree 1 0 Q" using jp by (simp only: Qw; simp)
 have Pweight: "v_degree (int 1) (-int 0) P=int p*int 1" using Pw by simp
 have Qweight: "v_degree (int 1) (-int 0) Q=int(1*j)" using Qw by simp
 have ratio: "\<not>v_degree 1 0 P dvd v_degree 1 0 Q" "\<not>v_degree 1 0 Q dvd v_degree 1 0 P"
   "v_degree 1 0 Q*int p=v_degree 1 0 P*int j"
   using primeMate_terminal_signed_ratio[where rho=1 and s=0, OF P Q p j _ cop Pweight Qweight] by simp_all
 have ending: "(p,2*p)\<in>biv_support(leading_form 1 0 P)"
   "\<forall>u\<in>biv_support(leading_form 1 0 P). pair_grade(p,2*p)\<le>pair_grade u"
   using horizontalFace_ending_endpoint[OF alpha mu pp Pf] by blast+
 have corner: "GGVPolynomialCornerInput" by (rule GGVInputs_corner[OF H])
 note chosen = corner[unfolded GGVPolynomialCornerInput_def,
   THEN spec[where x=P], THEN spec[where x=Q],
   THEN spec[where x="1::int"], THEN spec[where x="0::int"],
   THEN spec[where x=p], THEN spec[where x="2*p"],
   THEN spec[where x=j], THEN spec[where x=p], THEN spec[where x="2::nat"]]
 have sigma_nonpositive: "(0::int)\<le>0" by simp
 have p_gt_one: "1<p" using p2 by arith
 have h_two: "2\<le>(2::nat)" by simp
 note applied = chosen[THEN mp, OF pair, THEN mp, OF dir,
   THEN mp, OF sigma_nonpositive, THEN mp, OF common(1), THEN mp, OF common(2),
   THEN mp, OF Ppos, THEN mp, OF Qpos, THEN mp, OF ratio(1), THEN mp, OF ratio(2),
   THEN mp, OF ending(1), THEN mp, OF ending(2), THEN mp, OF ratio(3),
   THEN mp, OF j, THEN mp, OF p_gt_one, THEN mp, OF cop, THEN mp, OF h_two]
 have forbidden: "\<not>((of_nat p::rat)/ of_nat p= of_nat(2::nat)-1 \<and> (of_nat(2*p)::rat)/ of_nat p= of_nat(2::nat))"
   by (rule applied)
 have pnz: "(of_nat p::rat)\<noteq>0" using pp by simp
 have first: "(of_nat p::rat)/ of_nat p= of_nat(2::nat)-1" using pnz by simp
 have second: "(of_nat(2*p)::rat)/ of_nat p= of_nat(2::nat)" using pnz by (simp add: of_nat_mult)
 show False using forbidden first second by blast
qed

lemma horizontalFace_exclusion:
 fixes P Q::"complex poly_operator" and p::nat
 assumes H: "GGVInputs" and alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and p: "prime p"
 and Pf: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
 and pair: "is_counterexample_pair P Q"
 shows False
proof -
 obtain Q' j nu where pair': "is_counterexample_pair P Q'" and j: "1<j" and cop: "coprime j p" and nu: "nu\<noteq>0"
 and Qw: "v_degree 1 0 Q'=int j"
 and Qf: "leading_form 1 0 Q'=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
   using horizontal_prime_terminal[OF H mu p Pf pair] by blast
 show False by (rule horizontalPair_corner_contradiction[OF H alpha mu nu p j cop Pf Qw Qf pair'])
qed

end
