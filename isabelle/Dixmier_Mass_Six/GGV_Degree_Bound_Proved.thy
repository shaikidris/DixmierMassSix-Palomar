theory GGV_Degree_Bound_Proved
 imports "Small_Crossing_Exclusion"
   "Small_Crossing_Data_Assembly"
begin

lemma degreeMinimal_degree_bound_proved:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "15 < gcd(total_degree P)(total_degree Q)"
proof (rule ccontr)
 assume "\<not>15 < gcd(total_degree P)(total_degree Q)"
 then have small: "gcd(total_degree P)(total_degree Q)\<le>15" by arith
 obtain H where data: "ggv_small_degree_crossing_data P Q H"
  using degreeMinimal_small_degree_crossing_data[where P = P and Q = Q, OF minimal small] by blast
 show False by (rule smallDegreeCrossing_impossible[where P = P and Q = Q and H = H, OF data])
qed

lemma ggv_degree_bound_proved:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "15 < gcd(total_degree P)(total_degree Q)"
proof (rule degreeBound_of_minimalPair_bound[where P = P and Q = Q])
 show "\<And>R S. is_degree_minimal_counterexample_pair R S \<Longrightarrow>
   15 < gcd(total_degree R)(total_degree S)"
   by (rule degreeMinimal_degree_bound_proved)
 show "is_counterexample_pair P Q" by (rule pair)
qed

end
