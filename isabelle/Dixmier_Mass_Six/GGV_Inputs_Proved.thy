theory GGV_Inputs_Proved
 imports "GGV_Inputs"
   "One_Sided_Global_Generation"
   "GGV_Companion_Proved"
   "Universal_Diagonal_Case_Map"
   "GGV_Polynomial_Corner_Proved"
   "GGV_Cut_Corner_Proved"
   "GGV_Degree_Bound_Proved"
begin

lemma ggvInputs_of_degree_bound:
 assumes degree: "\<And>P Q::complex poly_operator. is_counterexample_pair P Q \<Longrightarrow> 15<gcd(total_degree P)(total_degree Q)"
 shows GGVInputs
proof -
 have grades: GGVGradesInput using ggv_grades_opposite_proved by (simp only: GGVGradesInput_def)
 have companion: GGVCompanionInput using ggv_companion_proved by (simp only: GGVCompanionInput_def)
 have cases: GGVCaseSplitInput unfolding GGVCaseSplitInput_def
  apply (rule ggv_caseSplit_of_companion_degree_fields)
   apply (rule ggv_companion_proved)
  apply (rule degree)
  apply assumption
  done
 have bound: GGVDegreeBoundInput using degree by (auto simp: GGVDegreeBoundInput_def)
 have cut: GGVCutCornerInput unfolding GGVCutCornerInput_def
  by (intro allI impI; rule ggv_cut_corner_proved; assumption)
 have corner: GGVPolynomialCornerInput using ggv_polynomial_corner_proved by (simp only: GGVPolynomialCornerInput_def)
 show ?thesis using grades companion cases bound cut corner unfolding GGVInputs_def by blast
qed

lemma ggvInputs_proved: GGVInputs
 by (rule ggvInputs_of_degree_bound; rule ggv_degree_bound_proved; assumption)

end
