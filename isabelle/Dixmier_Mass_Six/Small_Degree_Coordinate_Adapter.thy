theory Small_Degree_Coordinate_Adapter
 imports "Small_Degree_Companion_Properness"
begin

lemma small_degree_candidate_membership:
 "(((u,v),(f1,f2)),(r,s))\<in>ggvSmallDegreeCandidates \<longleftrightarrow>
   ((u,v),(f1,f2))\<in>factorPairs \<and> r<16 \<and> s<16 \<and> s<r \<and> r<u \<and>
   (let d=gcd (f1-1) (f2-1); rho=(f2-1) div d; t=(f1-1) div d
     in rho*u+t*s=rho*r+t*v)"
proof -
 have block: "((q,(r,s))\<in>set(small_degree_candidate_block p)) \<longleftrightarrow>
   q=p \<and> r<16 \<and> s<16 \<and> s<r \<and> r<fst(fst p) \<and>
   (let d=gcd (fst(snd p)-1) (snd(snd p)-1);
      rho=(snd(snd p)-1) div d; t=(fst(snd p)-1) div d
    in rho*fst(fst p)+t*s=rho*r+t*snd(fst p))" for p q r s
   unfolding small_degree_candidate_block_def
   by (simp only: set_filter set_concat_map_membership set_map set_upt)
      (auto simp: mem_Collect_eq UN_iff image_iff atLeastLessThan_iff
        fst_conv snd_conv case_prod_conv Let_def)
 show ?thesis
   unfolding ggvSmallDegreeCandidates_def small_degree_candidate_list_def factorPairs_def
   by (simp only: set_concat_map_membership)
      (auto simp only: UN_iff image_iff block fst_conv snd_conv)
qed

lemma ggv_small_degree_coordinates_forbidden_corner:
 fixes u v f1 f2 r s :: nat
 assumes main: "u<v" and degree: "u+v\<le>15" and first: "2\<le>f1"
   and proportional: "f1*v=f2*u" and crossing: "s<r" and predecessor: "r<u"
   and weight: "let d=gcd (f1-1) (f2-1); rho=(f2-1) div d; t=(f1-1) div d
     in rho*u+t*s=rho*r+t*v"
 shows "let d=gcd (f1-1) (f2-1); rho=(f2-1) div d; t=(f1-1) div d
   in d=1 \<and> 0<rho \<and> (\<exists>h::nat. 2\<le>h \<and> s\<le>h \<and>
     v=s+rho*h \<and> rho*r+(h-s)*t=rho*h-1)"
proof -
 have u_positive: "0<u" using predecessor by arith
 have v_positive: "0<v" using main u_positive by arith
 have first_positive: "0<f1" using first by arith
 have product_positive: "0<f1*v" using first_positive v_positive by simp
 have second_positive: "0<f2" using product_positive proportional
   by (auto simp: zero_less_mult_iff)
 let ?d = "gcd (f1-1) (f2-1)"
 let ?rho = "(f2-1) div ?d"
 let ?k = "(f1-1) div ?d"
 have companion: "?rho*f1+?k=?k*f2+?rho"
   using gcd_normalized_direction_companion_weight[OF first_positive second_positive]
   by (simp only: Let_def)
 have direction: "0<?k\<and>?k<?rho"
   using gcd_normalized_direction_strict[OF main first proportional]
   by (simp only: Let_def)
 have line: "?rho*u+?k*s=?rho*r+?k*v" using weight by (simp only: Let_def)
 have proper: "f1<u\<and>f2<v"
   by (rule companion_endpoint_both_proper_nat[OF conjunct1[OF direction]
     conjunct2[OF direction] u_positive v_positive crossing line companion proportional])
 have main_lower: "2<u" using first proper by arith
 have bounds: "u<16\<and>v<16\<and>f1<16\<and>f2<16\<and>r<16\<and>s<16"
   using degree main proper predecessor crossing by arith
 have factors: "((u,v),(f1,f2))\<in>factorPairs"
   by (simp only: factorPairs_membership smallPairs_membership fst_conv snd_conv;
     use main_lower main degree first proper proportional bounds in auto)
 have member: "(((u,v),(f1,f2)),(r,s))\<in>ggvSmallDegreeCandidates"
   by (simp only: small_degree_candidate_membership;
     use factors bounds crossing predecessor weight in auto)
 show ?thesis using ggvSmallDegreeCandidates_forbidden_corner[OF member]
   by (auto simp: fst_conv snd_conv Let_def)
qed

end
