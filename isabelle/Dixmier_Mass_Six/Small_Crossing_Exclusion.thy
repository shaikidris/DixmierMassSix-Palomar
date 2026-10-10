theory Small_Crossing_Exclusion
 imports "Small_Crossing_Cut_Multiplicity"
   "GGV_Cut_Corner_Proved"
   "GGV_Polynomial_Corner_Proved"
   "Counterexample_Positive_Weight"
begin

lemma smallDegreeCrossing_impossible:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows False
proof -
 let ?L="ggv_left H" let ?M="ggv_right H" let ?R="ggv_root H"
 let ?rho="ggv_rho H" let ?s="ggv_s H" let ?d="ggv_d H" let ?n="ggv_n H"
 let ?u="ggv_u H" let ?v="ggv_v H" let ?r="ggv_r H" let ?t="ggv_t H" let ?h="ggv_h H"
 let ?w="ggv_weight H"
 have minimal: "is_degree_minimal_counterexample_pair ?L ?M"
 and rho: "0< ?rho" and s: "0< ?s" and direction: "is_direction(int ?rho)(-int ?s)"
 and Ldir: "in_direction(int ?rho)(-int ?s) ?L" and Mdir: "in_direction(int ?rho)(-int ?s) ?M"
 and d: "1< ?d" and n: "1< ?n" and cop: "coprime ?d ?n" and R: "?R\<noteq>0"
 and nu: "ggv_nu H\<noteq>0" and mu: "ggv_mu H\<noteq>0"
 and hom: "weighted_homogeneous(int ?rho)(-int ?s) ?w ?R"
 and Lface: "leading_form(int ?rho)(-int ?s) ?L=[:[:ggv_nu H:]:] * ?R ^ ?d"
 and Mface: "leading_form(int ?rho)(-int ?s) ?M=[:[:ggv_mu H:]:] * ?R ^ ?n"
 and Lweight: "v_degree(int ?rho)(-int ?s) ?L=int ?d * ?w"
 and endpt: "(?u,?v)\<in>biv_support ?R" and start: "(?r,?t)\<in>biv_support ?R"
 and maximum: "\<forall>e\<in>biv_support ?R. fst e\<le> ?u"
 and minimum: "\<forall>e\<in>biv_support ?R. ?r\<le>fst e"
 and startcross: "?t< ?r" and endcross: "?u< ?v"
 and h: "2\<le> ?h" and t: "?t\<le> ?h"
 and corner: "?rho * ?r+(?h- ?t) * ?s= ?rho * ?h-1"
 using data unfolding ggv_small_degree_crossing_data_def by blast+
 have pair: "is_counterexample_pair ?L ?M" using minimal unfolding is_degree_minimal_counterexample_pair_def by blast
 have L: "?L\<in>weyl_algebra" and M: "?M\<in>weyl_algebra" using pair unfolding is_counterexample_pair_def by blast+
 have strict: "?s< ?rho" using direction by (simp add: is_direction_def)
 have rhoZ: "0<int ?rho" and sZ: "0<int ?s" and sumZ: "0<int ?rho-int ?s" using rho s strict by simp_all
 have homogeneous: "\<And>e. e\<in>biv_support ?R \<Longrightarrow> pair_weight(int ?rho)(-int ?s)e= ?w"
  using hom unfolding weighted_homogeneous_def by blast
 have grade: "0<pair_grade(?r,?t)" using startcross by (simp add: pair_grade_def)
 have direction_sum: "0<int ?rho+(-int ?s)" using sumZ by simp
 have raw_lower: "int ?rho\<le>pair_weight(int ?rho)(-int ?s)(?r,?t)"
   by (rule positive_grade_weight_ge_rho[where rho="int ?rho" and sigma="-int ?s" and a="(?r,?t)", OF rhoZ direction_sum grade])
 have wge: "int ?rho\<le> ?w"
   using raw_lower by (simp only: homogeneous[OF start])
 have positive_w: "0< ?w" using wge rhoZ by arith
 have endpointsL: "(?d * ?u,?d * ?v)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L) \<and>
 (?d * ?r,?d * ?t)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L) \<and>
 (\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L). fst e\<le> ?d * ?u) \<and>
 (\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L). ?d * ?r\<le>fst e)"
  by (rule leadingFace_power_endpoint_pair[OF L R nu s homogeneous endpt start])
   (use maximum minimum Lface in auto)
 have endpointsM: "(?n * ?u,?n * ?v)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M) \<and>
 (?n * ?r,?n * ?t)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M) \<and>
 (\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M). fst e\<le> ?n * ?u) \<and>
 (\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M). ?n * ?r\<le>fst e)"
  by (rule leadingFace_power_endpoint_pair[OF M R mu s homogeneous endpt start])
   (use maximum minimum Mface in auto)
 have Mh: "weighted_homogeneous(int ?rho)(-int ?s)(v_degree(int ?rho)(-int ?s) ?M)(leading_form(int ?rho)(-int ?s) ?M)"
  unfolding leading_form_def by (rule weighted_component_homogeneous)
 have Mpoint: "(?n * ?u,?n * ?v)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M)"
   by (rule conjunct1[OF endpointsM])
 have Mall: "\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M).
   pair_weight(int ?rho)(-int ?s)e=v_degree(int ?rho)(-int ?s) ?M"
   using Mh by (simp only: weighted_homogeneous_def)
 have Mtop: "pair_weight(int ?rho)(-int ?s)(?n * ?u,?n * ?v)=v_degree(int ?rho)(-int ?s) ?M"
   by (rule bspec[OF Mall Mpoint])
 have Mscale: "pair_weight(int ?rho)(-int ?s)(?n * ?u,?n * ?v)=
   int ?n * pair_weight(int ?rho)(-int ?s)(?u,?v)"
   by (simp add: pair_weight_def algebra_simps)
 have Mscaled: "pair_weight(int ?rho)(-int ?s)(?n * ?u,?n * ?v)=int ?n * ?w"
   using Mscale by (simp only: homogeneous[OF endpt])
 have Mweight: "v_degree(int ?rho)(-int ?s) ?M=int ?n * ?w"
   by (rule trans[OF sym[OF Mtop] Mscaled])
 have d_positive: "0< ?d" using d by arith
 have n_positive: "0< ?n" using n by arith
 have dZ: "0<int ?d" using d_positive by simp
 have nZ: "0<int ?n" using n_positive by simp
 have Lproduct: "0<int ?d * ?w" by (rule mult_pos_pos[OF dZ positive_w])
 have Mproduct: "0<int ?n * ?w" by (rule mult_pos_pos[OF nZ positive_w])
 have Lpos: "0<v_degree(int ?rho)(-int ?s) ?L"
   by (simp only: Lweight; rule Lproduct)
 have Mpos: "0<v_degree(int ?rho)(-int ?s) ?M"
   by (simp only: Mweight; rule Mproduct)
 have ratio: "v_degree(int ?rho)(-int ?s) ?M * int ?d=v_degree(int ?rho)(-int ?s) ?L * int ?n"
  by (simp add: Lweight Mweight mult_ac)
 have coprev: "coprime ?n ?d" using cop by (simp add: coprime_commute)
 have neither: "\<not>v_degree(int ?rho)(-int ?s) ?L dvd v_degree(int ?rho)(-int ?s) ?M \<and>
 \<not>v_degree(int ?rho)(-int ?s) ?M dvd v_degree(int ?rho)(-int ?s) ?L"
  by (rule coprime_positive_weight_ratio_neither_dvd[OF Lpos Mpos n d coprev ratio])
 have w_nonnegative: "0\<le> ?w" using positive_w by arith
 have d_two_nat: "2\<le> ?d" using d by arith
 have n_two_nat: "2\<le> ?n" using n by arith
 have d_two: "(2::int)\<le>int ?d" using d_two_nat by simp
 have n_two: "(2::int)\<le>int ?n" using n_two_nat by simp
 have left_large: "2 * ?w\<le>int ?d * ?w"
   by (rule mult_right_mono[OF d_two w_nonnegative])
 have right_large: "2 * ?w\<le>int ?n * ?w"
   by (rule mult_right_mono[OF n_two w_nonnegative])
 have threshold: "int ?rho-int ?s<v_degree(int ?rho)(-int ?s) ?L+v_degree(int ?rho)(-int ?s) ?M"
  using left_large right_large wge rhoZ sZ by (simp only: Lweight Mweight; arith)
 have d_endpoint_order: "?d * ?u< ?d * ?v"
   by (rule mult_strict_left_mono[OF endcross d_positive])
 have n_endpoint_order: "?n * ?u< ?n * ?v"
   by (rule mult_strict_left_mono[OF endcross n_positive])
 have d_endpoint_cast: "int(?d * ?u)<int(?d * ?v)" using d_endpoint_order by simp
 have n_endpoint_cast: "int(?n * ?u)<int(?n * ?v)" using n_endpoint_order by simp
 have negL: "pair_grade(?d * ?u,?d * ?v)<0"
   using d_endpoint_cast by (simp only: pair_grade_def fst_conv snd_conv; arith)
 have negM: "pair_grade(?n * ?u,?n * ?v)<0"
   using n_endpoint_cast by (simp only: pair_grade_def fst_conv snd_conv; arith)
 have Lhom: "weighted_homogeneous(int ?rho)(-int ?s)(v_degree(int ?rho)(-int ?s) ?L)(leading_form(int ?rho)(-int ?s) ?L)"
  unfolding leading_form_def by (rule weighted_component_homogeneous)
 have Lall: "\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L).
   pair_weight(int ?rho)(-int ?s)e=v_degree(int ?rho)(-int ?s) ?L"
   using Lhom by (simp only: weighted_homogeneous_def)
 have maximal_grade: "\<forall>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L). pair_grade e\<le>pair_grade(?d * ?r,?d * ?t)"
 proof (intro ballI)
  fix e assume e: "e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L)"
  have base: "(?d * ?r,?d * ?t)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L)" using endpointsL by blast
  have lower: "?d * ?r\<le>fst e" using endpointsL e by blast
  have e_weight: "pair_weight(int ?rho)(-int ?s)e=v_degree(int ?rho)(-int ?s) ?L"
    by (rule bspec[OF Lall e])
  have base_weight: "pair_weight(int ?rho)(-int ?s)(?d * ?r,?d * ?t)=v_degree(int ?rho)(-int ?s) ?L"
    by (rule bspec[OF Lall base])
  have same_weight: "pair_weight(int ?rho)(-int ?s)e=pair_weight(int ?rho)(-int ?s)(?d * ?r,?d * ?t)"
    by (rule trans[OF e_weight sym[OF base_weight]])
  have equation: "int ?s * (pair_grade(?d * ?r,?d * ?t)-pair_grade e)=
   (int ?rho-int ?s) * (int(fst e)-int(?d * ?r))"
    using same_weight by (simp add: pair_weight_def pair_grade_def algebra_simps; arith)
  have factor_nonnegative: "0\<le>int ?rho-int ?s" using sumZ by arith
  have lower_whole_cast: "int(?d * ?r)\<le>int(fst e)"
    by (rule iffD2[OF of_nat_le_iff lower])
  have lower_cast: "int ?d * int ?r\<le>int(fst e)"
    using lower_whole_cast by (simp only: of_nat_mult)
  have difference_nonnegative: "0\<le>int(fst e)-int(?d * ?r)" using lower_whole_cast by arith
  have nonnegative: "0\<le>(int ?rho-int ?s) * (int(fst e)-int(?d * ?r))"
    by (rule mult_nonneg_nonneg[OF factor_nonnegative difference_nonnegative])
  have scaled_nonnegative: "0\<le>int ?s * (pair_grade(?d * ?r,?d * ?t)-pair_grade e)"
    by (simp only: equation; rule nonnegative)
  have scaled_comparison: "int ?s * 0\<le>int ?s * (pair_grade(?d * ?r,?d * ?t)-pair_grade e)"
    by (simp only: mult_zero_right; rule scaled_nonnegative)
  have "0\<le>pair_grade(?d * ?r,?d * ?t)-pair_grade e"
    by (rule iffD1[OF mult_le_cancel_left_pos[OF sZ] scaled_comparison])
  then show "pair_grade e\<le>pair_grade(?d * ?r,?d * ?t)" by arith
 qed
 have threshold_sum: "int ?rho+(-int ?s)<v_degree(int ?rho)(-int ?s) ?L+v_degree(int ?rho)(-int ?s) ?M"
   using threshold by (simp only: diff_conv_add_uminus)
 have sigma_nonpositive: "-int ?s\<le>0" by simp
 have left_nondivisible: "\<not>v_degree(int ?rho)(-int ?s) ?L dvd v_degree(int ?rho)(-int ?s) ?M"
   by (rule conjunct1[OF neither])
 have right_nondivisible: "\<not>v_degree(int ?rho)(-int ?s) ?M dvd v_degree(int ?rho)(-int ?s) ?L"
   by (rule conjunct2[OF neither])
 have left_end: "(?d * ?u,?d * ?v)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L)"
   by (rule conjunct1[OF endpointsL])
 have right_end: "(?n * ?u,?n * ?v)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M)"
   by (rule conjunct1[OF endpointsM])
 have left_start: "(?d * ?r,?d * ?t)\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L)"
   by (rule conjunct1[OF conjunct2[OF endpointsL]])
 have left_negative: "\<exists>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?L). pair_grade e<0"
   by (rule bexI[where x="(?d * ?u,?d * ?v)"], rule negL, rule left_end)
 have right_negative: "\<exists>e\<in>biv_support(leading_form(int ?rho)(-int ?s) ?M). pair_grade e<0"
   by (rule bexI[where x="(?n * ?u,?n * ?v)"], rule negM, rule right_end)
 have forbidden: "\<not>(((of_nat(?d * ?r)+((of_nat(?d * ?t)::rat)- of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))) * of_int(-int ?s)/ of_int(int ?rho))/ of_nat ?d=
 of_nat ?h-1/ of_int(int ?rho)) \<and> (of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))::rat)/ of_nat ?d= of_nat ?h)"
   by (rule ggv_cut_corner_proved[where P="?L" and Q="?M" and rho="int ?rho" and sigma="-int ?s"
     and u="?d * ?r" and v="?d * ?t" and n="?n" and d="?d" and h="?h",
     OF pair direction rhoZ sigma_nonpositive Ldir Mdir Lpos Mpos threshold_sum
       left_nondivisible right_nondivisible left_negative right_negative left_start maximal_grade ratio n d coprev h])
 have maxmult: "max_root_mult(cut_poly(int ?rho)(-int ?s) ?L)= ?d * ?h"
  by (rule smallDegreeCrossing_cutPoly_maxRootMult[OF data])
 have positive_product: "0< ?rho * ?h" using rho h by (intro mult_pos_pos) arith+
 have corner_nat: "?rho * ?r+(?h- ?t) * ?s+1= ?rho * ?h" using corner positive_product by arith
 have corner_rat: "(of_nat ?rho::rat) * of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s+1= of_nat ?rho * of_nat ?h"
 proof -
  have "(of_nat ?rho::rat) * of_nat ?r+ of_nat(?h- ?t) * of_nat ?s+1= of_nat ?rho * of_nat ?h"
   using arg_cong[OF corner_nat, where f="\<lambda>x::nat. of_nat x::rat"] by simp
  then show ?thesis using t by (simp add: of_nat_diff)
 qed
 have rho_nonzero: "(of_nat ?rho::rat)\<noteq>0" using rho by simp
 have d_nonzero: "(of_nat ?d::rat)\<noteq>0" using d by simp
 have corner_rearranged: "(of_nat ?rho::rat) * of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s=
   of_nat ?rho * of_nat ?h-1" using corner_rat by arith
 have scalar_coordinate: "(of_nat ?r::rat)+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho=
   of_nat ?h-1/ of_nat ?rho"
 proof -
   have expanded: "((of_nat ?rho * of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s)::rat)/ of_nat ?rho=
     of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho"
     by (simp only: add_divide_distrib times_divide_eq_left[symmetric] divide_self[OF rho_nonzero] mult_1_left)
   have reduced: "((of_nat ?rho * of_nat ?h-1)::rat)/ of_nat ?rho= of_nat ?h-1/ of_nat ?rho"
     by (simp only: diff_divide_distrib times_divide_eq_left[symmetric] divide_self[OF rho_nonzero] mult_1_left)
   have transport: "((of_nat ?rho * of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s)::rat)/ of_nat ?rho=
     (of_nat ?rho * of_nat ?h-1)/ of_nat ?rho"
     by (simp only: corner_rearranged)
   show ?thesis by (rule trans[OF sym[OF expanded] trans[OF transport reduced]])
 qed
 have numerator: "(of_nat ?d * of_nat ?r+(of_nat ?d * of_nat ?t- of_nat ?d * of_nat ?h) * (- of_nat ?s)/ of_nat ?rho::rat)=
   of_nat ?d * (of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho)"
   by (simp only: divide_inverse algebra_simps mult_minus_left mult_minus_right left_minus right_minus add_0_left add_0_right)
 have cancellation: "(of_nat ?d * (of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho)::rat)/ of_nat ?d=
   of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho"
   by (simp only: times_divide_eq_left[symmetric] divide_self[OF d_nonzero] mult_1_left)
 have cast_coordinate: "((of_nat(?d * ?r)+((of_nat(?d * ?t)::rat)- of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))) * of_int(-int ?s)/ of_int(int ?rho))/ of_nat ?d=
   (of_nat ?d * of_nat ?r+(of_nat ?d * of_nat ?t- of_nat ?d * of_nat ?h) * (- of_nat ?s)/ of_nat ?rho)/ of_nat ?d)"
   by (simp only: maxmult of_nat_mult of_int_minus of_int_of_nat_eq)
 have divided_numerator: "((of_nat ?d * of_nat ?r+(of_nat ?d * of_nat ?t- of_nat ?d * of_nat ?h) * (- of_nat ?s)/ of_nat ?rho)::rat)/ of_nat ?d=
   (of_nat ?d * (of_nat ?r+(of_nat ?h- of_nat ?t) * of_nat ?s/ of_nat ?rho))/ of_nat ?d"
   by (rule arg_cong[where f="\<lambda>z::rat. z/ of_nat ?d", OF numerator])
 have first_coordinate: "((of_nat(?d * ?r)+((of_nat(?d * ?t)::rat)- of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))) * of_int(-int ?s)/ of_int(int ?rho))/ of_nat ?d=
   of_nat ?h-1/ of_int(int ?rho))"
   using trans[OF cast_coordinate trans[OF divided_numerator trans[OF cancellation scalar_coordinate]]]
   by (simp only: of_int_of_nat_eq)
 have second_coordinate: "(of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))::rat)/ of_nat ?d= of_nat ?h"
   by (simp only: maxmult of_nat_mult times_divide_eq_left[symmetric] divide_self[OF d_nonzero] mult_1_left)
 have coordinates: "((of_nat(?d * ?r)+((of_nat(?d * ?t)::rat)- of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))) * of_int(-int ?s)/ of_int(int ?rho))/ of_nat ?d=
 of_nat ?h-1/ of_int(int ?rho)) \<and> (of_nat(max_root_mult(cut_poly(int ?rho)(-int ?s) ?L))::rat)/ of_nat ?d= of_nat ?h"
   by (rule conjI[OF first_coordinate second_coordinate])
 show False using forbidden coordinates by blast
qed

end
