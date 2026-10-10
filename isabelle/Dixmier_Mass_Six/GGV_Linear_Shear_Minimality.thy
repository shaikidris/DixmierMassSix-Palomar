theory GGV_Linear_Shear_Minimality
 imports "Degree_Minimal_Nondivisibility"
   "Polynomial_Cut_Translation"
begin

lemma degreeMinimal_pair_of_same_total_degrees:
 fixes P Q R S::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and pair: "is_counterexample_pair R S"
   and R: "total_degree R=total_degree P" and S: "total_degree S=total_degree Q"
 shows "is_degree_minimal_counterexample_pair R S"
 using minimal pair unfolding is_degree_minimal_counterexample_pair_def
 by (simp only: R S; blast)

lemma polynomial_linear_cut_totalDeg_and_translate:
 fixes P Q R S::"complex poly_operator" and c::complex
 assumes pair: "is_counterexample_pair P Q" and recovered: "is_counterexample_pair R S"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 1 c (polynomial_ramified_lift 1 P)"
 shows "total_degree R=total_degree P \<and>
   cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:c,1:]"
proof -
 have P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   using pair recovered by (simp_all add: is_counterexample_pair_def)
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 1 P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Rpositive: "0<v_degree 1 1 R"
   by (rule counterexample_vDeg_pos_all_directions[OF recovered direction])
 have Pnz: "P\<noteq>0" using positive by auto
 have transport: "v_degree 1 1 R=v_degree 1 1 P \<and>
   cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:c,1:]"
   using polynomial_monomial_cut_weight_and_translate[OF P R Pnz,
     where sigma=1 and c=c] positive Rpositive recover by simp
 have equality: "int(total_degree R)=int(total_degree P)"
   using transport counterexample_diagonal_weight_eq_total_degree[OF pair]
     counterexample_diagonal_weight_eq_total_degree[OF recovered] by simp
 show ?thesis using equality transport by simp
qed

lemma degreeMinimal_linear_cut_recovers_pair:
 fixes P Q::"complex poly_operator" and c::complex
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:c,1:] \<and>
   cut_poly 1 1 S=pcompose (cut_poly 1 1 Q) [:c,1:] \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 1 c (polynomial_ramified_lift 1 P) \<and>
   polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 1 c (polynomial_ramified_lift 1 Q)"
proof -
 have pair: "is_counterexample_pair P Q"
   using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 obtain R S where RS: "is_counterexample_pair R S"
   and recoverR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 1 c (polynomial_ramified_lift 1 P)"
   and recoverS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 1 c (polynomial_ramified_lift 1 Q)"
   using polynomial_monomial_cut_recovers_polynomial_counterexample[OF pair, where sigma=1 and c=c]
   by (simp; blast)
 have Rt: "total_degree R=total_degree P \<and>
   cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:c,1:]"
   by (rule polynomial_linear_cut_totalDeg_and_translate[OF pair RS recoverR])
 have St: "total_degree S=total_degree Q \<and>
   cut_poly 1 1 S=pcompose (cut_poly 1 1 Q) [:c,1:]"
   by (rule polynomial_linear_cut_totalDeg_and_translate[OF isCounterexamplePair_swap_neg[OF pair]
     isCounterexamplePair_swap_neg[OF RS] recoverS])
 have minRS: "is_degree_minimal_counterexample_pair R S"
   by (rule degreeMinimal_pair_of_same_total_degrees[OF minimal RS]) (use Rt St in blast)+
 show ?thesis by (intro exI[of _ R] exI[of _ S]) (use minRS Rt St recoverR recoverS in blast)
qed

lemma degreeMinimal_fourier_preserved:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "is_degree_minimal_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)"
proof -
 have pair: "is_counterexample_pair P Q"
   using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   using pair by (simp_all add: is_counterexample_pair_def)
 show ?thesis by (rule degreeMinimal_pair_of_same_total_degrees[OF minimal
   isCounterexamplePair_fourier[OF pair] totalDeg_fourier_eq[OF P] totalDeg_fourier_eq[OF Q]])
qed

end
