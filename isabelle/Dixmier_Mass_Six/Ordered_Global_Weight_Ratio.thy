theory Ordered_Global_Weight_Ratio
 imports Paired_Successor_Weight_Ratios
   "Subrectangular_Case_Support"
begin

definition ggv_negative_face_pair_ratio::"complex poly_operator\<Rightarrow>complex poly_operator\<Rightarrow>rat\<Rightarrow>rat" where
 "ggv_negative_face_pair_ratio = (\<lambda>(P::complex poly_operator) (Q::complex poly_operator) (t::rat).
 of_int(v_degree (rational_denominator t)(rational_numerator t) Q)/
 of_int(v_degree (rational_denominator t)(rational_numerator t) P))"

lemma face_ratio_of_integer_weight_equation:
 fixes p q::int and n d::nat
 assumes p: "p\<noteq>0" and d: "d\<noteq>0" and equation: "p*int n=q*int d"
 shows "(of_int q/ of_int p::rat)= of_nat n/ of_nat d"
proof -
 have converted: "(of_int p::rat)* of_nat n= of_int q* of_nat d"
   using arg_cong[where f="\<lambda>z::int. of_int z::rat", OF equation] by simp
 have pnz: "(of_int p::rat)\<noteq>0" and dnz: "(of_nat d::rat)\<noteq>0" using p d by simp_all
 show ?thesis using converted pnz dnz by (simp add: field_simps mult.commute)
qed

lemma counterexample_ordered_adjacent_ratio_eq:
 fixes P Q::"complex poly_operator" and j::nat
 assumes pair: "is_counterexample_pair P Q" and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
 shows "ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!j)=
   ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!(j+1))"
proof -
 let ?L="ggv_ordered_negative_face_slopes P"
 have i0: "j<length ?L" using index by arith
 have m1: "?L!j\<in>set ?L" by (rule nth_mem[OF i0])
 have m2: "?L!(j+1)\<in>set ?L" by (rule nth_mem[OF index])
 have dir1: "is_direction(rational_denominator(?L!j))(rational_numerator(?L!j))"
   using ggv_ordered_negative_entry_canonical_face[OF m1] by blast
 have dir2: "is_direction(rational_denominator(?L!(j+1)))(rational_numerator(?L!(j+1)))"
   using ggv_ordered_negative_entry_canonical_face[OF m2] by blast
 have p1: "v_degree(rational_denominator(?L!j))(rational_numerator(?L!j)) P\<noteq>0"
   using counterexample_vDeg_pos_all_directions[OF pair dir1] by arith
 have p2: "v_degree(rational_denominator(?L!(j+1)))(rational_numerator(?L!(j+1))) P\<noteq>0"
   using counterexample_vDeg_pos_all_directions[OF pair dir2] by arith
 obtain n d where dp: "0<d" and e1:
   "v_degree(rational_denominator(?L!j))(rational_numerator(?L!j)) P*int n=
    v_degree(rational_denominator(?L!j))(rational_numerator(?L!j)) Q*int d"
   and e2: "v_degree(rational_denominator(?L!(j+1)))(rational_numerator(?L!(j+1))) P*int n=
    v_degree(rational_denominator(?L!(j+1)))(rational_numerator(?L!(j+1))) Q*int d"
   using counterexample_ordered_adjacent_common_weight_ratio[OF pair index] by blast
 have dnz: "d\<noteq>0" using dp by arith
 have r1: "ggv_negative_face_pair_ratio P Q (?L!j)=(of_nat n/ of_nat d::rat)"
   unfolding ggv_negative_face_pair_ratio_def by (rule face_ratio_of_integer_weight_equation[OF p1 dnz e1])
 have r2: "ggv_negative_face_pair_ratio P Q (?L!(j+1))=(of_nat n/ of_nat d::rat)"
   unfolding ggv_negative_face_pair_ratio_def by (rule face_ratio_of_integer_weight_equation[OF p2 dnz e2])
 show ?thesis using r1 r2 by simp
qed

lemma counterexample_ordered_ratio_eq_first:
 fixes P Q::"complex poly_operator" and i::nat
 assumes pair: "is_counterexample_pair P Q" and index: "i<length(ggv_ordered_negative_face_slopes P)"
 shows "ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!i)=
   ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!0)"
 using index
proof (induction i)
 case 0 show ?case by simp
next
 case (Suc k)
 have k: "k<length(ggv_ordered_negative_face_slopes P)" using Suc.prems by arith
 have next_index: "k+1<length(ggv_ordered_negative_face_slopes P)"
   using Suc.prems by (simp only: Suc_eq_plus1)
 have adjacent: "ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!k)=
   ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!Suc k)"
   using counterexample_ordered_adjacent_ratio_eq[where P=P and Q=Q and j=k, OF pair next_index]
   by (simp only: Suc_eq_plus1)
 show ?case by (rule trans[OF adjacent[symmetric] Suc.IH[OF k]])
qed

lemma counterexample_ordered_ratio_eq_horizontal:
 fixes P Q::"complex poly_operator" and i::nat
 assumes pair: "is_counterexample_pair P Q" and index: "i<length(ggv_ordered_negative_face_slopes P)"
 shows "ggv_negative_face_pair_ratio P Q (ggv_ordered_negative_face_slopes P!i)=
   (of_int(v_degree 1 0 Q)/ of_int(v_degree 1 0 P)::rat)"
proof -
 let ?L="ggv_ordered_negative_face_slopes P" let ?j="length ?L-1" let ?t="?L!?j"
 have j: "?j<length ?L" and last: "?j+1=length ?L" using index by arith+
 have member: "?t\<in>set ?L" by (rule nth_mem[OF j])
 obtain rho s::nat where rho: "0<rho" and s: "0<s" and direction: "is_direction(int rho)(-int s)"
   and face: "in_direction(int rho)(-int s) P" and entry: "?t=(of_int(-int s)/ of_int(int rho)::rat)"
   and denominator: "int rho=rational_denominator ?t" and numerator: "-int s=rational_numerator ?t"
   using ggv_ordered_negative_entry_nat_face[OF member] by blast
 obtain n d where dp: "0<d" and negative_equation:
   "v_degree(int rho)(-int s) P*int n=v_degree(int rho)(-int s) Q*int d"
   and horizontal_equation: "v_degree 1 0 P*int n=v_degree 1 0 Q*int d"
   using counterexample_last_negative_horizontal_common_weight_ratio[OF pair rho s direction last entry face] by blast
 have pnz: "v_degree(int rho)(-int s) P\<noteq>0" using counterexample_vDeg_pos_all_directions[OF pair direction] by arith
 have horizontal: "is_direction 1 0" by (simp add: is_direction_def)
 have hnz: "v_degree 1 0 P\<noteq>0" using counterexample_vDeg_pos_all_directions[OF pair horizontal] by arith
 have dnz: "d\<noteq>0" using dp by arith
 have nr: "ggv_negative_face_pair_ratio P Q ?t=(of_nat n/ of_nat d::rat)"
   unfolding ggv_negative_face_pair_ratio_def
   by (simp only: denominator[symmetric] numerator[symmetric]; rule face_ratio_of_integer_weight_equation[OF pnz dnz negative_equation])
 have hr: "(of_int(v_degree 1 0 Q)/ of_int(v_degree 1 0 P)::rat)= of_nat n/ of_nat d"
   by (rule face_ratio_of_integer_weight_equation[OF hnz dnz horizontal_equation])
 have first: "ggv_negative_face_pair_ratio P Q (?L!i)=ggv_negative_face_pair_ratio P Q (?L!0)"
   by (rule counterexample_ordered_ratio_eq_first[OF pair index])
 have lastfirst: "ggv_negative_face_pair_ratio P Q ?t=ggv_negative_face_pair_ratio P Q (?L!0)"
   by (rule counterexample_ordered_ratio_eq_first[OF pair j])
 show ?thesis using first lastfirst nr hr by simp
qed

lemma counterexample_native_negative_ratio_eq_horizontal:
 fixes P Q::"complex poly_operator" and rho s j::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho"
   and direction: "is_direction(int rho)(-int s)"
   and index: "j<length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
 shows "(of_int(v_degree(int rho)(-int s) Q)/ of_int(v_degree(int rho)(-int s) P)::rat)=
   of_int(v_degree 1 0 Q)/ of_int(v_degree 1 0 P)"
proof -
 let ?t="ggv_ordered_negative_face_slopes P!j"
 have member: "?t\<in>set(ggv_ordered_negative_face_slopes P)" by (rule nth_mem[OF index])
 have canon: "is_direction(rational_denominator ?t)(rational_numerator ?t)" and cp: "0<rational_denominator ?t"
   using ggv_ordered_negative_entry_canonical_face[OF member] by blast+
 have rp: "0<int rho" using rho by simp
 have slope: "(of_int(-int s)/ of_int(int rho)::rat)= of_int(rational_numerator ?t)/ of_int(rational_denominator ?t)"
   by (simp only: rational_direction_ratio entry[symmetric])
 have normalized: "int rho=rational_denominator ?t \<and> -int s=rational_numerator ?t"
   by (rule ggv_primitive_negative_normal_unique[OF direction canon rp cp slope])
 show ?thesis using counterexample_ordered_ratio_eq_horizontal[OF pair index] normalized
   by (simp add: ggv_negative_face_pair_ratio_def)
qed

lemma subrectangular_totalDeg_eq:
 fixes P::"complex poly_operator" and a b::nat
 assumes rectangle: "is_subrectangular_at P a b"
 shows "total_degree P=a+b"
proof -
 have corner: "(a,b)\<in>biv_support(pbw_symbol P)" and bounded:
   "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
   using rectangle unfolding is_subrectangular_at_def by blast+
 have member: "a+b\<in>insert 0 ((\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P))"
   using imageI[OF corner, where f="\<lambda>e. fst e+snd e"] by simp
 have upper: "z\<le>a+b" if z: "z\<in>insert 0 ((\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P))" for z
 proof (cases "z=0")
  case True then show ?thesis by simp
 next
  case False
  have image: "z\<in>(\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P)" using z False by auto
  obtain e where e: "e\<in>biv_support(pbw_symbol P)" and eq: "z=fst e+snd e"
    by (rule imageE[OF image]) metis
  have e_bound: "fst e\<le>a \<and> snd e\<le>b" by (rule bounded[OF e])
  show ?thesis using e_bound by (simp only: eq; arith)
 qed
 show ?thesis unfolding total_degree_def
 proof (rule Max_eqI)
  show "finite(insert 0 ((\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P)))" by simp
  show "z\<le>a+b" if "z\<in>insert 0 ((\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P))" for z
    by (rule upper[OF that])
  show "a+b\<in>insert 0 ((\<lambda>e. fst e+snd e)`biv_support(pbw_symbol P))" by (rule member)
 qed
qed

lemma counterexample_subrectangular_negative_total_degree_ratio:
 fixes P Q::"complex poly_operator" and rho s j a b u v::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho"
   and direction: "is_direction(int rho)(-int s)"
   and index: "j<length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
   and a: "0<a" and P: "is_subrectangular_at P a b" and Q: "is_subrectangular_at Q u v"
   and proportion: "a*v=b*u"
 shows "v_degree(int rho)(-int s) Q*int(total_degree P)=
   v_degree(int rho)(-int s) P*int(total_degree Q)"
proof -
 have ratio: "(of_int(v_degree(int rho)(-int s) Q)/ of_int(v_degree(int rho)(-int s) P)::rat)= of_nat u/ of_nat a"
   using counterexample_native_negative_ratio_eq_horizontal[OF pair rho direction index entry]
     subrectangular_v_degree[OF P] subrectangular_v_degree[OF Q] by simp
 have positive: "0<v_degree(int rho)(-int s) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have pnz: "(of_int(v_degree(int rho)(-int s) P)::rat)\<noteq>0" using positive by simp
 have anz: "(of_nat a::rat)\<noteq>0" using a by simp
 have rational_cross: "(of_int(v_degree(int rho)(-int s) Q)::rat)* of_nat a= of_nat u* of_int(v_degree(int rho)(-int s) P)"
   using ratio pnz anz by (simp add: field_simps mult.commute)
 have lifted_cross: "(of_int(v_degree(int rho)(-int s) Q*int a)::rat)=
     of_int(int u*v_degree(int rho)(-int s) P)"
   using rational_cross by (simp only: of_int_mult of_int_of_nat_eq)
 have cross: "v_degree(int rho)(-int s) Q*int a=int u*v_degree(int rho)(-int s) P"
   using lifted_cross by (simp only: of_int_eq_iff)
 have proportional: "int a*int v=int b*int u" using proportion by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
 have multiplier: "int a*(v_degree(int rho)(-int s) Q*int(a+b)-v_degree(int rho)(-int s) P*int(u+v))=0"
 proof -
   have "int a*(v_degree(int rho)(-int s) Q*int(a+b)-v_degree(int rho)(-int s) P*int(u+v))=
     (v_degree(int rho)(-int s) Q*int a-int u*v_degree(int rho)(-int s) P)*int(a+b)+
     v_degree(int rho)(-int s) P*(int b*int u-int a*int v)" by (simp add: algebra_simps)
   also have "...=0" by (simp only: cross proportional; simp)
   finally show ?thesis .
 qed
 have cancellation: "v_degree(int rho)(-int s) Q*int(a+b)=v_degree(int rho)(-int s) P*int(u+v)"
   using multiplier a by auto
 show ?thesis by (simp only: subrectangular_totalDeg_eq[OF P] subrectangular_totalDeg_eq[OF Q]; rule cancellation)
qed
end
