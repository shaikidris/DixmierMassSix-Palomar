theory GGV_Minimal_Standardization
 imports "GGV_Minimal_Diagonal_Degree"
   "GGV_Two_Root_Standardization"
   "GGV_Pure_Linear_Minimal_Exclusion"
   "GGV_Diagonal_Root_Budget"
   "Positive_Singleton_Case_Dispatch"
begin

lemma degreeMinimal_subrectangular_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S a b u v. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<a \<and> 0<b \<and> 0<u \<and> 0<v \<and>
   is_subrectangular_at R a b \<and> is_subrectangular_at S u v \<and> a*v=b*u"
proof -
 obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
   and Rdegree: "total_degree R=total_degree P" and Sdegree: "total_degree S=total_degree Q"
   and full: "degree(cut_poly 1 1 R)=total_degree R"
   using degreeMinimal_full_degree_diagonal_cut_pair[OF minimal] by blast
 have pairRS: "is_counterexample_pair R S" using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have alternatives: "(\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 1 R=[:lam:]) \<or>
   (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^k) \<or>
   (\<exists>lam alpha beta::complex. \<exists>a b::nat. lam\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>a \<and> 1\<le>b \<and>
     cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^a*[:-beta,1:]^b)"
   by (rule preliminary_diagonal_cut_factorization[OF preliminary_companion_from_actual_GGV_companion pairRS])
 from alternatives show ?thesis
 proof (elim disjE)
   assume constant_case: "\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 1 R=[:lam:]"
   obtain lam where cut: "cut_poly 1 1 R=[:lam:]" using constant_case by blast
   have zero: "total_degree R=0" using full by (simp add: cut)
   have direction: "is_direction 1 1" by (simp add: is_direction_def)
   have positive: "0<v_degree 1 1 R" by (rule counterexample_vDeg_pos_all_directions[OF pairRS direction])
   show ?thesis using positive by (simp only: counterexample_diagonal_weight_eq_total_degree[OF pairRS] zero; simp)
 next
   assume pure: "\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^k"
   obtain lam alpha k where lam: "lam\<noteq>0" and cut: "cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^k" using pure by blast
   have degree: "total_degree R=k" using full by (simp add: cut lam degree_linear_power)
   show ?thesis by (rule FalseE[OF degreeMinimal_pure_linear_diagonal_impossible[OF minRS lam degree cut]])
 next
   assume two: "\<exists>lam alpha beta::complex. \<exists>a b::nat. lam\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>a \<and> 1\<le>b \<and>
     cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^a*[:-beta,1:]^b"
   obtain lam alpha beta a b where lam: "lam\<noteq>0" and distinct: "alpha\<noteq>beta" and amin: "1\<le>a" and bmin: "1\<le>b"
     and cut: "cut_poly 1 1 R=[:lam:]*[:-alpha,1:]^a*[:-beta,1:]^b" using two by blast
   have ap: "0<a" and bp: "0<b" using amin bmin by arith+
   have degree: "total_degree R=a+b" using full by (simp add: cut lam degree_mult_eq degree_linear_power)
   obtain T U u v where minTU: "is_degree_minimal_counterexample_pair T U"
     and Tdegree: "total_degree T=total_degree R" and Udegree: "total_degree U=total_degree S"
     and up: "0<u" and vp: "0<v" and rectangleT: "is_subrectangular_at T a b"
     and rectangleU: "is_subrectangular_at U u v" and proportional: "a*v=b*u"
     using degreeMinimal_two_root_subrectangular_pair[OF minRS lam distinct ap bp degree cut] by blast
   have TdegreeP: "total_degree T=total_degree P" by (simp only: Tdegree Rdegree)
   have UdegreeQ: "total_degree U=total_degree Q" by (simp only: Udegree Sdegree)
   show ?thesis by (rule exI[of _ T], rule exI[of _ U], rule exI[of _ a], rule exI[of _ b], rule exI[of _ u], rule exI[of _ v])
     (use minTU TdegreeP UdegreeQ ap bp up vp rectangleT rectangleU proportional in blast)
 qed
qed

lemma degreeMinimal_oriented_subrectangular_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S a b u v. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<a \<and> a<b \<and> 0<u \<and> 0<v \<and>
   is_subrectangular_at R a b \<and> is_subrectangular_at S u v \<and> a*v=b*u"
proof -
 obtain R S a b u v where minRS: "is_degree_minimal_counterexample_pair R S"
   and Rdegree: "total_degree R=total_degree P" and Sdegree: "total_degree S=total_degree Q"
   and ap: "0<a" and bp: "0<b" and up: "0<u" and vp: "0<v"
   and rectangleR: "is_subrectangular_at R a b" and rectangleS: "is_subrectangular_at S u v"
   and proportional: "a*v=b*u"
   using degreeMinimal_subrectangular_pair[OF minimal] by blast
 have pairRS: "is_counterexample_pair R S" using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra" using pairRS by (simp_all add: is_counterexample_pair_def)
 have positive: "0<a+b" using ap by arith
 have unequal: "a\<noteq>b" by (rule counterexample_subrectangular_corner_not_diagonal[OF preliminary_companion_from_actual_GGV_companion pairRS rectangleR positive])
 show ?thesis
 proof (cases "a<b")
   case True show ?thesis by (rule exI[of _ R], rule exI[of _ S], rule exI[of _ a], rule exI[of _ b], rule exI[of _ u], rule exI[of _ v])
     (use minRS Rdegree Sdegree ap True up vp rectangleR rectangleS proportional in blast)
 next
   case False
   have oriented: "b<a" using False unequal by arith
   have positiveS: "0<u+v" using up by arith
   have minF: "is_degree_minimal_counterexample_pair (fourier_alg_hom R) (fourier_alg_hom S)" by (rule degreeMinimal_fourier_preserved[OF minRS])
   have rectangleFR: "is_subrectangular_at (fourier_alg_hom R) b a" by (rule subrectangular_fourier_at[OF R rectangleR positive])
   have rectangleFS: "is_subrectangular_at (fourier_alg_hom S) v u" by (rule subrectangular_fourier_at[OF S rectangleS positiveS])
   show ?thesis by (rule exI[of _ "fourier_alg_hom R"], rule exI[of _ "fourier_alg_hom S"], rule exI[of _ b], rule exI[of _ a], rule exI[of _ v], rule exI[of _ u])
     (use minF Rdegree Sdegree bp oriented vp up rectangleFR rectangleFS proportional
       in \<open>simp add: totalDeg_fourier_eq[OF R] totalDeg_fourier_eq[OF S]\<close>)
 qed
qed

end
