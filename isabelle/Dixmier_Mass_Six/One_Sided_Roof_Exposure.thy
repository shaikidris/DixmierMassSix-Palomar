theory One_Sided_Roof_Exposure
  imports Newton_Roof_Support
begin

definition exponent_total :: "nat\<times>nat \<Rightarrow> nat" where
  "exponent_total d=fst d+snd d"

lemma roof_exposing_weight:
  "pair_weight (N+1) (1-N) d=N*pair_grade d+int(exponent_total d)"
  by (simp add: pair_weight_def pair_grade_def exponent_total_def algebra_simps)

lemma exists_positive_grade_exponent_in_integerPositiveNewtonRoof:
  fixes T::"complex poly_operator"
  assumes positive: "\<exists>d\<in>biv_support (pbw_symbol T). 0<pair_grade d"
  shows "\<exists>d\<in>biv_support (pbw_symbol T). 0<pair_grade d \<and>
    exponent_point d\<in>integer_positive_newton_roof T"
proof -
  let ?S = "biv_support (pbw_symbol T)"
  let ?g = "Max (pair_grade ` ?S)"
  obtain dpos where dpos: "dpos\<in>?S" and pos: "0<pair_grade dpos" using positive by blast
  have finiteS: "finite ?S" by simp
  have grade_mem: "?g\<in>pair_grade ` ?S"
    by (rule Max_in) (use finiteS dpos in auto)
  obtain dg where dg: "dg\<in>?S" and dgg: "pair_grade dg=?g" using grade_mem by auto
  have grade_max: "\<And>e. e\<in>?S \<Longrightarrow> pair_grade e\<le>?g"
    by (rule Max_ge) (use finiteS in auto)
  have gpos: "0<?g" using pos grade_max[OF dpos] by arith
  let ?Sg = "{e\<in>?S. pair_grade e=?g}"
  have finiteSg: "finite ?Sg" using finiteS by simp
  have dgSg: "dg\<in>?Sg" using dg dgg by simp
  have nonemptySg: "?Sg\<noteq>{}" using dgSg by blast
  have total_mem: "Max (exponent_total ` ?Sg)\<in>exponent_total ` ?Sg"
    by (rule Max_in) (use finiteSg nonemptySg in auto)
  obtain d where dSg: "d\<in>?Sg" and dtotal: "exponent_total d=Max (exponent_total ` ?Sg)"
    using total_mem by auto
  have dS: "d\<in>?S" and dg: "pair_grade d=?g" using dSg by auto
  have total_max: "\<And>e. e\<in>?Sg \<Longrightarrow> exponent_total e\<le>exponent_total d"
    unfolding dtotal by (rule Max_ge) (use finiteSg in auto)
  let ?M = "Max (exponent_total ` ?S)"
  let ?N = "int ?M+1"
  have total_bound: "\<And>e. e\<in>?S \<Longrightarrow> exponent_total e\<le>?M"
    by (rule Max_ge) (use finiteS in auto)
  have Nnonneg: "0\<le>?N" by simp
  have max_weight: "\<And>e. e\<in>?S \<Longrightarrow>
    pair_weight (?N+1) (1-?N) e\<le>pair_weight (?N+1) (1-?N) d"
  proof -
    fix e assume e: "e\<in>?S"
    show "pair_weight (?N+1) (1-?N) e\<le>pair_weight (?N+1) (1-?N) d"
    proof (cases "pair_grade e=?g")
      case True
      have "exponent_total e\<le>exponent_total d" by (rule total_max) (use e True in auto)
      then show ?thesis by (simp only: roof_exposing_weight True dg; simp)
    next
      case False
      have gap: "pair_grade e\<le>?g-1" using grade_max[OF e] False by arith
      have mul: "?N*pair_grade e\<le>?N*(?g-1)" by (rule mult_left_mono[OF gap Nnonneg])
      have total: "int(exponent_total e)\<le>int ?M" using total_bound[OF e] by simp
      have strict: "?N*(?g-1)+int ?M<?N*?g" by (simp add: algebra_simps)
      have "?N*pair_grade e+int(exponent_total e)<?N*?g" using mul total strict by arith
      then show ?thesis by (simp only: roof_exposing_weight dg; arith)
    qed
  qed
  have face: "d\<in>biv_support (leading_form (?N+1) (1-?N) T)"
    by (rule symbol_maximizer_mem_leading_form[OF dS max_weight])
  have point: "exponent_point d\<in>convex hull
    (exponent_point ` biv_support (leading_form (?N+1) (1-?N) T))"
    by (rule hull_inc) (use face in auto)
  have roof: "exponent_point d\<in>integer_positive_newton_roof T"
    unfolding integer_positive_newton_roof_def
    by (intro CollectI exI[of _ "?N+1"] exI[of _ "1-?N"] conjI) (use point in auto)
  show ?thesis
  proof (rule bexI[where x=d], intro conjI)
    show "0<pair_grade d" using dg gpos by simp
    show "exponent_point d\<in>integer_positive_newton_roof T" by (rule roof)
    show "d\<in>?S" by (rule dS)
  qed
qed

end
