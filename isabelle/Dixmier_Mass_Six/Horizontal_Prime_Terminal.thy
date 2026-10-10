theory Horizontal_Prime_Terminal
 imports Horizontal_Mate_Descent
begin

lemma horizontal_mate_exponent_ne_one:
 fixes P Q::"complex poly_operator" and j::nat
 assumes H: "GGVInputs" and nu: "nu\<noteq>0" and direction: "is_direction 1 0"
 and pair: "is_counterexample_pair P Q"
 and Qf: "leading_form 1 0 Q=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
 shows "j\<noteq>1"
proof
 assume one: "j=1"
 have swap: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have companion: "GGVCompanionInput" by (rule GGVInputs_companion[OF H])
 obtain a k S F m where a: "a\<noteq>0" and k: "2\<le>k" and S: "S\<noteq>0"
 and face: "leading_form 1 0 Q=[:[:a:]:]*S^k"
   using companion swap direction unfolding GGVCompanionInput_def by blast
 have equality: "[:[:nu:]:]*crossing_primitive_base alpha 2 1 0=[:[:a:]:]*S^k"
   using face by (simp only: Qf one power_one_right)
 show False using horizontalBase_not_proper_power[OF nu a k S] equality by contradiction
qed

lemma horizontal_prime_terminal:
 fixes P Q::"complex poly_operator" and p::nat
 assumes H: "GGVInputs" and mu: "mu\<noteq>0" and p: "prime p"
 and Pf: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
 and pair: "is_counterexample_pair P Q"
 shows "\<exists>Q'::complex poly_operator. \<exists>j::nat. \<exists>nu::complex.
 is_counterexample_pair P Q' \<and>1<j \<and>coprime j p \<and>nu\<noteq>0 \<and>
 v_degree 1 0 Q'=int j \<and>
 leading_form 1 0 Q'=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Pw: "v_degree 1 0 P=int p" by (rule horizontalFace_weight[OF P mu Pf])
 have p2: "2\<le>p" by (rule prime_ge_2_nat[OF p])
 obtain Q' j nu where pair': "is_counterexample_pair P Q'" and j: "0<j"
 and notdividing: "\<not>p dvd j" and nu: "nu\<noteq>0"
 and weight: "v_degree 1 0 Q'=int j"
 and face: "leading_form 1 0 Q'=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
   using horizontal_mate_descent_terminal[OF H mu p2 Pw Pf pair] by blast
 have direction: "is_direction (1::int) 0" by (simp add: is_direction_def)
 have notone: "j\<noteq>1" by (rule horizontal_mate_exponent_ne_one[OF H nu direction pair' face])
 have greater: "1<j" using j notone by arith
 have coprime: "coprime j p" by (rule primeMateExponent_coprime[OF p notdividing])
 show ?thesis by (rule exI[where x=Q'], rule exI[where x=j], rule exI[where x=nu], intro conjI)
   (rule pair' greater coprime nu weight face)+
qed

end
