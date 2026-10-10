theory Small_Crossing_Data_Assembly
 imports "Small_Crossing_Data_Carrier"
   "GGV_Minimal_Crossing_Pair"
   "Common_Root_Occupied_Endpoints"
begin

lemma degreeMinimal_small_degree_crossing_data:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and small: "gcd(total_degree P)(total_degree Q)\<le>15"
 shows "\<exists>H. ggv_small_degree_crossing_data P Q H"
proof - 
 obtain A B a b c e j rho s E G where minAB: "is_degree_minimal_counterexample_pair A B"
   and degreeA: "total_degree A = total_degree P" and degreeB: "total_degree B = total_degree Q"
   and a: "0 < a" and rectA: "is_subrectangular_at A a b" and rectB: "is_subrectangular_at B c e"
   and rectangle_proportional: "a * e = b * c" and index: "j < length(ggv_ordered_negative_face_slopes A)"
   and rho: "0 < rho" and s: "0 < s" and direction: "is_direction(int rho)( - int s)"
   and entry: "ggv_ordered_negative_face_slopes A!j = (of_int( - int s) / of_int(int rho)::rat)"
   and faceA: "in_direction(int rho)( - int s) A" and faceB: "in_direction(int rho)( - int s) B"
   and E: "E\<in>biv_support(leading_form(int rho)( - int s) A)"
   and G: "G\<in>biv_support(leading_form(int rho)( - int s) A)"
   and Emin: "\<And>x. x\<in>biv_support(leading_form(int rho)( - int s) A) \<Longrightarrow> snd E\<le>snd x"
   and Gmax: "\<And>x. x\<in>biv_support(leading_form(int rho)( - int s) A) \<Longrightarrow> snd x\<le>snd G"
   and Epos: "0 < pair_grade E" and Gneg: "pair_grade G < 0"
   using degreeMinimal_strict_crossing_pair[where P = P and Q = Q, OF minimal] by blast
 obtain d n R nu mu w where d: "1 < d" and n: "1 < n" and primitive: "coprime d n"
   and Ad: "total_degree A = d * gcd(total_degree A)(total_degree B)"
   and Bd: "total_degree B = n * gcd(total_degree A)(total_degree B)"
   and R: "R\<noteq>0" and nu: "nu\<noteq>0" and mu: "mu\<noteq>0"
   and Rhom: "weighted_homogeneous(int rho)( - int s) w R"
   and weight: "v_degree(int rho)( - int s) A = int d * w"
   and Af: "leading_form(int rho)( - int s) A = [:[:nu:]:] * R^d"
   and Bf: "leading_form(int rho)( - int s) B = [:[:mu:]:] * R^n"
   using degreeMinimal_subrectangular_negative_common_root[where P = A and Q = B and rho = rho and s = s and j = j and a = a and b = b and u = c and v = e, OF minAB rho direction index entry a rectA rectB rectangle_proportional] by blast
 have pairAB: "is_counterexample_pair A B" using minAB by (simp add: is_degree_minimal_counterexample_pair_def)
 have A: "A\<in>weyl_algebra" using pairAB by (simp add: is_counterexample_pair_def)
 have dp: "0 < d" using d by arith
 have Rhom_pointwise: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight(int rho)( - int s) x = w"
   using Rhom unfolding weighted_homogeneous_def by blast
 have Af_scalar: "leading_form(int rho)( - int s) A = smult [:nu:] (R^d)" using Af by simp
 obtain u v r t where endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
   and max: "\<forall>x\<in>biv_support R. fst x\<le>u" and min: "\<forall>x\<in>biv_support R. r\<le>fst x"
   and tr: "t < r" and uv: "u < v" and ru: "r < u" and bounded: "u + v\<le>gcd(total_degree A)(total_degree B)"
   using negative_face_root_crossing_and_gcd_bound[where P = A and Q = B and R = R and nu = nu and rho = rho and s = s and m = d and w = w and e = E and f = G, OF A rho s dp R nu Rhom_pointwise Af_scalar Ad E G Emin Gmax Epos Gneg] by blast
 have smallroot: "u + v\<le>15" using bounded small by (simp only: degreeA degreeB; arith)
 have maximum_root: "\<And>x. x\<in>biv_support R \<Longrightarrow> fst x\<le>u" by (rule bspec[OF max])
 have companion_available: "\<exists>F::complex bivariate. \<exists>f1 f2 h::nat.
   weighted_homogeneous(int rho)( - int s)(int rho - int s) F \<and>
   biv_poisson R F = R \<and> (1,1)\<in>biv_support F \<and>
   (f1,f2)\<in>biv_support F \<and> (\<forall>x\<in>biv_support F. fst x\<le>f1) \<and>
   2\<le>f1 \<and> f1 * v = f2 * u \<and> gcd(f1 - 1)(f2 - 1) = 1 \<and>
   2\<le>h \<and> t\<le>h \<and> v = t + rho * h \<and>
   rho * r + (h - t) * s = rho * h - 1"
 proof (rule counterexample_crossing_root_small_degree_coordinates[
     where P = A and Q = B and R = R and nu = nu and rho = rho and s = s
       and m = d and u = u and v = v and r = r and t = t and w = w])
   show "is_counterexample_pair A B" by (rule pairAB)
   show "0 < s" by (rule s)
   show "0 < d" by (rule dp)
   show "is_direction(int rho)( - int s)" by (rule direction)
   show "R\<noteq>0" by (rule R)
   show "nu\<noteq>0" by (rule nu)
   show "weighted_homogeneous(int rho)( - int s) w R" by (rule Rhom)
   show "leading_form(int rho)( - int s) A = [:[:nu:]:] * R^d" by (rule Af)
   show "(u,v)\<in>biv_support R" by (rule endpt)
   show "(r,t)\<in>biv_support R" by (rule start)
   show "\<And>x. x\<in>biv_support R \<Longrightarrow> fst x\<le>u" by (rule maximum_root)
   show "t < r" by (rule tr)
   show "u < v" by (rule uv)
   show "r < u" by (rule ru)
   show "u + v\<le>15" by (rule smallroot)
 qed
 obtain F f1 f2 h where companion_facts: "(weighted_homogeneous(int rho)( - int s)(int rho - int s) F) \<and>
   (biv_poisson R F = R) \<and>
   ((1,1)\<in>biv_support F) \<and>
   ((f1,f2)\<in>biv_support F) \<and>
   (\<forall>x\<in>biv_support F. fst x\<le>f1) \<and>
   (2\<le>f1) \<and>
   (f1 * v = f2 * u) \<and>
   (gcd(f1 - 1)(f2 - 1) = 1) \<and>
   (2\<le>h) \<and>
   (t\<le>h) \<and>
   (v = t + rho * h) \<and>
   (rho * r + (h - t) * s = rho * h - 1)"
   using companion_available
 proof (elim exE)
   fix F::"complex bivariate" and f1 f2 h::nat
   assume tuple: "(weighted_homogeneous(int rho)( - int s)(int rho - int s) F) \<and>
   (biv_poisson R F = R) \<and>
   ((1,1)\<in>biv_support F) \<and>
   ((f1,f2)\<in>biv_support F) \<and>
   (\<forall>x\<in>biv_support F. fst x\<le>f1) \<and>
   (2\<le>f1) \<and>
   (f1 * v = f2 * u) \<and>
   (gcd(f1 - 1)(f2 - 1) = 1) \<and>
   (2\<le>h) \<and>
   (t\<le>h) \<and>
   (v = t + rho * h) \<and>
   (rho * r + (h - t) * s = rho * h - 1)"
   show thesis by (rule that[OF tuple])
 qed
 have Fhom: "weighted_homogeneous(int rho)( - int s)(int rho - int s) F" by (rule conjunct1[OF companion_facts])
 have bracket: "biv_poisson R F = R" by (rule conjunct1[OF conjunct2[OF companion_facts]])
 have base: "(1,1)\<in>biv_support F" by (rule conjunct1[OF conjunct2[OF conjunct2[OF companion_facts]]])
 have Fend: "(f1,f2)\<in>biv_support F" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]])
 have Fmax: "\<forall>x\<in>biv_support F. fst x\<le>f1" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]])
 have first: "2\<le>f1" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]])
 have proportional: "f1 * v = f2 * u" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]])
 have step: "gcd(f1 - 1)(f2 - 1) = 1" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]]])
 have h: "2\<le>h" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]]]])
 have th: "t\<le>h" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]]]]])
 have vh: "v = t + rho * h" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]]]]]])
 have corner: "rho * r + (h - t) * s = rho * h - 1" by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF companion_facts]]]]]]]]]]])
 let ?H = "\<lparr>ggv_left = A,ggv_right = B,ggv_rho = rho,ggv_s = s,ggv_d = d,ggv_n = n,
   ggv_u = u,ggv_v = v,ggv_r = r,ggv_t = t,ggv_h = h,ggv_f1 = f1,ggv_f2 = f2,
   ggv_root = R,ggv_companion = F,ggv_nu = nu,ggv_mu = mu,ggv_weight = w\<rparr>"
 have actual: "ggv_small_degree_crossing_data P Q ?H"
   using minAB degreeA degreeB rho s direction faceA faceB d n primitive R nu mu Rhom Af Bf weight
     endpt start max min tr uv ru smallroot Fhom bracket base Fend Fmax first proportional step h th vh corner
   by (simp add: ggv_small_degree_crossing_data_def)
 show ?thesis by (rule exI[of _ ?H], rule actual)
qed
end
