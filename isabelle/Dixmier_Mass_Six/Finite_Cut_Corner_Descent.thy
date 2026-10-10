theory Finite_Cut_Corner_Descent
 imports Finite_Cut_Corner_State
   "Corner_Finite_Directions"
begin

lemma finiteCutCornerState_impossible:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
 and Q: "Q\<in>weyl_algebra" and exact: "op_comp Q P-op_comp P Q=id"
 and d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h" and cop: "coprime d n"
 and state: "finite_cut_corner_state l P Q n d h cuts rho sigma"
 shows False
proof -
 let ?S="{v::int\<times>int. \<exists>cs. finite_cut_corner_state l P Q n d h cs (fst v) (snd v)}"
 have subset: "?S\<subseteq>corner_admissible_directions l"
 proof
   fix v assume "v\<in>?S"
   then obtain cs where st: "finite_cut_corner_state l P Q n d h cs (fst v) (snd v)" by blast
   have divides: "fst v dvd int l"
     by (rule finiteCutCornerState_rho_dvd_index[OF l P Q exact d n h cop st])
   show "v\<in>corner_admissible_directions l"
     using st divides unfolding finite_cut_corner_state_def corner_admissible_directions_def by blast
 qed
 have initial_member: "(rho,sigma)\<in>?S" using state by auto
 have nonempty: "?S\<noteq>{}" using initial_member by blast
 have successor: "\<And>v. v\<in>?S \<Longrightarrow> \<exists>w\<in>?S.
   of_int(snd w)/ of_int(fst w)<(of_int(snd v)/ of_int(fst v)::rat)"
 proof -
   fix v assume "v\<in>?S"
   then obtain cs where st: "finite_cut_corner_state l P Q n d h cs (fst v) (snd v)" by blast
   obtain a r s where strict: "fst v*s<r*snd v"
     and successor_state: "finite_cut_corner_state l P Q n d h (a#cs) r s"
     using finiteCutCornerState_lower_successor[OF l P Q exact d n h cop st] by blast
   have old_positive: "0<fst v" and new_positive: "0<r"
     using st successor_state unfolding finite_cut_corner_state_def by blast+
   have old_rat: "(0::rat)< of_int(fst v)" and new_rat: "(0::rat)< of_int r"
     using old_positive new_positive by simp_all
   have cross: "(of_int s::rat) * of_int(fst v)< of_int(snd v) * of_int r"
     using strict by (simp only: mult.commute of_int_mult [symmetric] of_int_less_iff)
   have slope: "(of_int s::rat)/ of_int r< of_int(snd v)/ of_int(fst v)"
   proof -
     have "(of_int s::rat)<(of_int(snd v)/ of_int(fst v)) * of_int r"
       using cross old_rat by (simp add: pos_less_divide_eq times_divide_eq_right mult.commute)
     then show ?thesis using new_rat by (simp only: pos_divide_less_eq)
   qed
   show "\<exists>w\<in>?S. of_int(snd w)/ of_int(fst w)<(of_int(snd v)/ of_int(fst v)::rat)"
     by (rule bexI[of _ "(r,s)"]) (use successor_state slope in auto)
 qed
 show False by (rule corner_no_total_lower_successor[OF l subset nonempty successor])
qed

end
