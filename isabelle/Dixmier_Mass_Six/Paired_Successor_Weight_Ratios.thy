theory Paired_Successor_Weight_Ratios
 imports Paired_Endpoint_Weight_Ratios
begin

lemma counterexample_paired_successor_shared_endpoints:
 fixes P Q::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int and j::nat
 assumes pair: "is_counterexample_pair P Q" and dir1: "is_direction rho1 sigma1"
   and dir2: "is_direction rho2 sigma2" and neg1: "sigma1<0" and neg2: "sigma2<0"
   and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
   and first: "ggv_ordered_negative_face_slopes P!j=(of_int sigma1/ of_int rho1::rat)"
   and second: "ggv_ordered_negative_face_slopes P!(j+1)=(of_int sigma2/ of_int rho2::rat)"
   and face1: "in_direction rho1 sigma1 P" and face2: "in_direction rho2 sigma2 P"
 shows "(\<exists>a. a\<in>biv_support(leading_form rho1 sigma1 P) \<and>
 a\<in>biv_support(leading_form rho2 sigma2 P) \<and>
 (\<forall>e\<in>biv_support(leading_form rho1 sigma1 P). snd e\<le>snd a) \<and>
 (\<forall>e\<in>biv_support(leading_form rho2 sigma2 P). snd a\<le>snd e)) \<and>
 (\<exists>b. b\<in>biv_support(leading_form rho1 sigma1 Q) \<and>
 b\<in>biv_support(leading_form rho2 sigma2 Q) \<and>
 (\<forall>e\<in>biv_support(leading_form rho1 sigma1 Q). snd e\<le>snd b) \<and>
 (\<forall>e\<in>biv_support(leading_form rho2 sigma2 Q). snd b\<le>snd e))"
proof -
 have rp1: "0<rho1" using dir1 neg1 by (simp add: is_direction_def; arith)
 have rp2: "0<rho2" using dir2 neg2 by (simp add: is_direction_def; arith)
 have index0: "j<length(ggv_ordered_negative_face_slopes P)" using index by arith
 have mem1: "ggv_ordered_negative_face_slopes P!j\<in>set(ggv_ordered_negative_face_slopes P)" by (rule nth_mem[OF index0])
 have mem2: "ggv_ordered_negative_face_slopes P!(j+1)\<in>set(ggv_ordered_negative_face_slopes P)" by (rule nth_mem[OF index])
 have left: "-1<(of_int sigma1/ of_int rho1::rat)" using ggv_ordered_negative_slope_bounds[OF mem1] by (simp only: first; blast)
 have right: "(of_int sigma2/ of_int rho2::rat)<0" using ggv_ordered_negative_slope_bounds[OF mem2] by (simp only: second; blast)
 have Qface1: "in_direction rho1 sigma1 Q" using counterexample_strict_negative_InDir_iff[OF pair dir1 neg1] face1 by blast
 have Qface2: "in_direction rho2 sigma2 Q" using counterexample_strict_negative_InDir_iff[OF pair dir2 neg2] face2 by blast
 have lists: "ggv_ordered_negative_face_slopes P=ggv_ordered_negative_face_slopes Q" by (rule ggv_ordered_negative_slopes_eq[OF pair])
 have Qindex: "j+1<length(ggv_ordered_negative_face_slopes Q)" using index by (simp only: lists)
 have Qfirst: "ggv_ordered_negative_face_slopes Q!j=(of_int sigma1/ of_int rho1::rat)" using first by (simp only: lists)
 have Qsecond: "ggv_ordered_negative_face_slopes Q!(j+1)=(of_int sigma2/ of_int rho2::rat)" using second by (simp only: lists)
 show ?thesis by (intro conjI)
   (rule leadingFace_successor_shared_endpoint[OF rp1 rp2 left right index first second face1 face2],
    rule leadingFace_successor_shared_endpoint[OF rp1 rp2 left right Qindex Qfirst Qsecond Qface1 Qface2])
qed

lemma counterexample_paired_successor_proportional_vertices:
 fixes P Q::"complex poly_operator" and rho1 s1 rho2 s2 j::nat
 assumes pair: "is_counterexample_pair P Q" and rho1: "0<rho1" and s1: "0<s1" and s2: "0<s2"
   and dir1: "is_direction (int rho1) (-int s1)" and dir2: "is_direction (int rho2) (-int s2)"
   and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
   and first: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s1)/ of_int(int rho1)::rat)"
   and second: "ggv_ordered_negative_face_slopes P!(j+1)=(of_int(-int s2)/ of_int(int rho2)::rat)"
   and face1: "in_direction (int rho1) (-int s1) P" and face2: "in_direction (int rho2) (-int s2) P"
 shows "\<exists>a b. \<exists>n d::nat.
 a\<in>biv_support(leading_form (int rho1) (-int s1) P) \<and>
 a\<in>biv_support(leading_form (int rho2) (-int s2) P) \<and>
 b\<in>biv_support(leading_form (int rho1) (-int s1) Q) \<and>
 b\<in>biv_support(leading_form (int rho2) (-int s2) Q) \<and>
 0<n \<and> 0<d \<and> coprime d n \<and> n*fst a=d*fst b \<and> n*snd a=d*snd b"
proof -
 have neg1: "-int s1<0" and neg2: "-int s2<0" using s1 s2 by simp_all
 obtain a b where a1: "a\<in>biv_support(leading_form (int rho1) (-int s1) P)"
   and a2: "a\<in>biv_support(leading_form (int rho2) (-int s2) P)"
   and b1: "b\<in>biv_support(leading_form (int rho1) (-int s1) Q)"
   and b2: "b\<in>biv_support(leading_form (int rho2) (-int s2) Q)"
   and amax: "\<And>e. e\<in>biv_support(leading_form (int rho1) (-int s1) P) \<Longrightarrow> snd e\<le>snd a"
   and bmax: "\<And>e. e\<in>biv_support(leading_form (int rho1) (-int s1) Q) \<Longrightarrow> snd e\<le>snd b"
   using counterexample_paired_successor_shared_endpoints[OF pair dir1 dir2 neg1 neg2 index first second face1 face2] by blast
 obtain n d where n: "0<n" and d: "0<d" and cop: "coprime d n"
   and x: "n*fst a=d*fst b" and y: "n*snd a=d*snd b"
   using counterexample_negative_face_maxima_proportional[OF pair rho1 s1 dir1 a1 b1 amax bmax] by blast
 show ?thesis using a1 a2 b1 b2 n d cop x y by blast
qed

lemma counterexample_paired_successor_common_weight_ratio:
 fixes P Q::"complex poly_operator" and rho1 s1 rho2 s2 j::nat
 assumes pair: "is_counterexample_pair P Q" and rho1: "0<rho1" and s1: "0<s1" and s2: "0<s2"
   and dir1: "is_direction (int rho1) (-int s1)" and dir2: "is_direction (int rho2) (-int s2)"
   and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
   and first: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s1)/ of_int(int rho1)::rat)"
   and second: "ggv_ordered_negative_face_slopes P!(j+1)=(of_int(-int s2)/ of_int(int rho2)::rat)"
   and face1: "in_direction (int rho1) (-int s1) P" and face2: "in_direction (int rho2) (-int s2) P"
 shows "\<exists>n d::nat. 0<n \<and> 0<d \<and> coprime d n \<and>
 v_degree (int rho1) (-int s1) P*int n=v_degree (int rho1) (-int s1) Q*int d \<and>
 v_degree (int rho2) (-int s2) P*int n=v_degree (int rho2) (-int s2) Q*int d"
proof -
 obtain a b n d where a1: "a\<in>biv_support(leading_form (int rho1) (-int s1) P)"
   and a2: "a\<in>biv_support(leading_form (int rho2) (-int s2) P)"
   and b1: "b\<in>biv_support(leading_form (int rho1) (-int s1) Q)"
   and b2: "b\<in>biv_support(leading_form (int rho2) (-int s2) Q)"
   and n: "0<n" and d: "0<d" and cop: "coprime d n"
   and x: "n*fst a=d*fst b" and y: "n*snd a=d*snd b"
   using counterexample_paired_successor_proportional_vertices[OF pair rho1 s1 s2 dir1 dir2 index first second face1 face2] by blast
 have weights: "v_degree (int rho1) (-int s1) P*int n=v_degree (int rho1) (-int s1) Q*int d \<and>
   v_degree (int rho2) (-int s2) P*int n=v_degree (int rho2) (-int s2) Q*int d"
   by (rule paired_face_points_common_weight_ratio[
     where P=P and Q=Q and a=a and b=b and n=n and d=d,
     OF a1 a2 b1 b2 x y])
 show ?thesis by (rule exI[where x=n], rule exI[where x=d])
   (intro conjI n d cop conjunct1[OF weights] conjunct2[OF weights])
qed

lemma counterexample_ordered_adjacent_common_weight_ratio:
 fixes P Q::"complex poly_operator" and j::nat
 assumes pair: "is_counterexample_pair P Q" and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
 shows "\<exists>n d::nat. 0<n \<and> 0<d \<and> coprime d n \<and>
 v_degree (rational_denominator(ggv_ordered_negative_face_slopes P!j))
   (rational_numerator(ggv_ordered_negative_face_slopes P!j)) P*int n=
 v_degree (rational_denominator(ggv_ordered_negative_face_slopes P!j))
   (rational_numerator(ggv_ordered_negative_face_slopes P!j)) Q*int d \<and>
 v_degree (rational_denominator(ggv_ordered_negative_face_slopes P!(j+1)))
   (rational_numerator(ggv_ordered_negative_face_slopes P!(j+1))) P*int n=
 v_degree (rational_denominator(ggv_ordered_negative_face_slopes P!(j+1)))
   (rational_numerator(ggv_ordered_negative_face_slopes P!(j+1))) Q*int d"
proof -
 let ?L="ggv_ordered_negative_face_slopes P"
 have index0: "j<length ?L" using index by arith
 have m1: "?L!j\<in>set ?L" by (rule nth_mem[OF index0])
 have m2: "?L!(j+1)\<in>set ?L" by (rule nth_mem[OF index])
 obtain rho1 s1::nat where rho1: "0<rho1" and s1: "0<s1"
   and dir1: "is_direction (int rho1) (-int s1)" and face1: "in_direction (int rho1) (-int s1) P"
   and first: "?L!j=(of_int(-int s1)/ of_int(int rho1)::rat)"
   and r1: "int rho1=rational_denominator(?L!j)" and n1: "-int s1=rational_numerator(?L!j)"
   using ggv_ordered_negative_entry_nat_face[OF m1] by blast
 obtain rho2 s2::nat where s2: "0<s2"
   and dir2: "is_direction (int rho2) (-int s2)" and face2: "in_direction (int rho2) (-int s2) P"
   and second: "?L!(j+1)=(of_int(-int s2)/ of_int(int rho2)::rat)"
   and r2: "int rho2=rational_denominator(?L!(j+1))" and n2: "-int s2=rational_numerator(?L!(j+1))"
   using ggv_ordered_negative_entry_nat_face[OF m2] by blast
 show ?thesis using counterexample_paired_successor_common_weight_ratio[OF pair rho1 s1 s2 dir1 dir2 index first second face1 face2]
   by (simp only: r1 n1 r2 n2)
qed
end
