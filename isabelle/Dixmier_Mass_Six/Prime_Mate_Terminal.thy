theory Prime_Mate_Terminal
 imports "Crossing_Mate_Descent_Terminal"
  "Pure_Power_Arithmetic"
begin

lemma crossingFace_mate_exponent_ne_one:
 fixes P Q::"complex poly_operator" and q rho s j::nat
 assumes H: "GGVInputs" and s: "0<s" and nu: "nu\<noteq>0"
 and direction: "is_direction (int rho) (-int s)"
 and pair: "is_counterexample_pair P Q"
 and Qf: "leading_form (int rho) (-int s) Q=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
 shows "j\<noteq>1"
proof
 assume one: "j=1"
 have swap: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have companion: "GGVCompanionInput" by (rule GGVInputs_companion[OF H])
 obtain a k S F m where a: "a\<noteq>0" and k: "2\<le>k" and S: "S\<noteq>0"
 and face: "leading_form (int rho) (-int s) Q=[:[:a:]:]*S^k"
   using companion swap direction unfolding GGVCompanionInput_def by blast
 have equality: "[:[:nu:]:]*crossing_primitive_base alpha q rho s=[:[:a:]:]*S^k"
   using face by (simp only: Qf one power_one_right)
 show False using crossingBase_not_proper_power[OF s nu a k S] equality by contradiction
qed

lemma crossingFace_prime_terminal:
 fixes P Q::"complex poly_operator" and p q rho s::nat
 assumes H: "GGVInputs" and mu: "mu\<noteq>0" and p: "prime p"
 and s: "0<s" and sr: "s<rho" and direction: "is_direction (int rho) (-int s)"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and pair: "is_counterexample_pair P Q"
 shows "\<exists>Q'::complex poly_operator. \<exists>j::nat. \<exists>nu::complex.
 is_counterexample_pair P Q' \<and>1<j \<and>coprime j p \<and>nu\<noteq>0 \<and>
 v_degree (int rho) (-int s) Q'=int(rho*j) \<and>
 leading_form (int rho) (-int s) Q'=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
proof -
 have p2: "2\<le>p" by (rule prime_ge_2_nat[OF p])
 obtain Q' j nu where pair': "is_counterexample_pair P Q'" and j: "0<j"
 and notdividing: "\<not>p dvd j" and nu: "nu\<noteq>0"
 and weight: "v_degree (int rho) (-int s) Q'=int(rho*j)"
 and face: "leading_form (int rho) (-int s) Q'=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
   using crossingFace_mate_descent_terminal[OF H mu p2 s sr Pw Pf pair] by blast
 have notone: "j\<noteq>1" by (rule crossingFace_mate_exponent_ne_one[OF H s nu direction pair' face])
 have greater: "1<j" using j notone by arith
 have coprime: "coprime j p" by (rule primeMateExponent_coprime[OF p notdividing])
 show ?thesis by (rule exI[where x=Q'], rule exI[where x=j], rule exI[where x=nu], intro conjI)
   (rule pair' greater coprime nu weight face)+
qed

lemma primeMate_terminal_signed_ratio:
 fixes P Q::"complex poly_operator" and p j rho s::nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and p: "prime p" and j: "1<j" and rho: "0<rho" and cop: "coprime j p"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Qw: "v_degree (int rho) (-int s) Q=int(rho*j)"
 shows "\<not>v_degree (int rho) (-int s) P dvd v_degree (int rho) (-int s) Q \<and>
 \<not>v_degree (int rho) (-int s) Q dvd v_degree (int rho) (-int s) P \<and>
 v_degree (int rho) (-int s) Q*int p=v_degree (int rho) (-int s) P*int j \<and>
 (of_int(v_degree (int rho) (-int s) Q)::rat)/ of_int(v_degree (int rho) (-int s) P)= of_nat j/ of_nat p"
proof -
 have notdividing: "\<not>p dvd j"
 proof
   assume divides: "p dvd j"
   have unit: "p=1" by (rule coprime_common_divisor_nat[OF cop divides]) simp
   show False using unit prime_gt_1_nat[OF p] by arith
 qed
 have signed: "\<not>int p*int rho dvd int j*int rho \<and>\<not>int j*int rho dvd int p*int rho"
   by (rule primeMateWeights_nonintegral_int[OF p j rho notdividing])
 have Qdegree: "v_degree (int rho) (-int s) Q=int j*int rho"
   by (simp only: Qw of_nat_mult mult.commute)
 have forward: "\<not>v_degree (int rho) (-int s) P dvd v_degree (int rho) (-int s) Q"
   unfolding Pw Qdegree by (rule conjunct1[OF signed])
 have backward: "\<not>v_degree (int rho) (-int s) Q dvd v_degree (int rho) (-int s) P"
   unfolding Pw Qdegree by (rule conjunct2[OF signed])
 have cross: "v_degree (int rho) (-int s) Q*int p=v_degree (int rho) (-int s) P*int j"
   by (simp only: Pw Qw of_nat_mult; simp add: algebra_simps)
 have ratio: "(of_int(v_degree (int rho) (-int s) Q)::rat)/ of_int(v_degree (int rho) (-int s) P)= of_nat j/ of_nat p"
   using primeMateWeight_ratio[where j=j, OF p rho]
   by (simp only: Pw Qw of_int_mult of_int_of_nat_eq of_nat_mult mult.commute)
 show ?thesis by (intro conjI) (rule forward backward cross ratio)+
qed

end
