theory Primitive_Polynomial_Corner
 imports Companion_Endpoint_Properness
begin

lemma homogeneous_companion_end_nonprimitive:
 fixes R F::"complex bivariate" and rho s u v r t f1 f2::nat and degree::int
 assumes s: "0<s" and direction: "is_direction (int rho) (-int s)"
 and Rhom: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and Fhom: "\<And>d. d\<in>biv_support F \<Longrightarrow> pair_weight (int rho) (-int s) d=int rho-int s"
 and Rend: "(u,v)\<in>biv_support R" and Rstart: "(r,t)\<in>biv_support R"
 and Rmax: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 and Fend: "(f1,f2)\<in>biv_support F"
 and Fmax: "\<And>d. d\<in>biv_support F \<Longrightarrow> fst d\<le>f1"
 and companion: "biv_poisson R F=R"
 and start: "0<pair_grade (r,t)" and endpt: "pair_grade (u,v)<0"
 shows "f1<u \<and> f2<v \<and> 1<gcd u v"
proof -
 have tr: "t<r" using start by (simp add: pair_grade_def)
 have uv: "u<v" using endpt by (simp add: pair_grade_def)
 have ru: "r\<le>u" using Rmax[OF Rstart] by simp
 have up: "0<u" using tr ru by arith
 have vp: "0<v" using up uv by arith
 have sr: "s<rho" using direction by (simp add: is_direction_def)
 have Rnz: "R\<noteq>0" using Rstart by auto
 have base: "(1,1)\<in>biv_support F" by (rule homogeneous_companion_base_mem[OF s sr Rnz Fhom companion])
 have nonmonomial: "1<card(biv_support F)"
   by (rule crossing_poisson_companion_nonmonomial[OF base companion Rstart Rend start endpt])
 have f1: "2\<le>f1"
   by (rule homogeneous_companion_end_x_ge_two[OF s direction Fhom base Fmax nonmonomial])
 have endpoint_proportional: "f1*v=f2*u"
   by (rule homogeneous_companion_end_proportional[OF s f1 Rhom Fhom Rend Fend Rmax Fmax companion])
 have line: "rho*u+s*t=rho*r+s*v"
   by (rule homogeneous_endpoints_weight_equation[OF Rhom Rend Rstart])
 have comp: "rho*f1+s=s*f2+rho"
   using homogeneous_endpoints_weight_equation[OF Fhom Fend base] by simp
 have proper: "f1<u \<and> f2<v"
   by (rule companion_endpoint_both_proper_nat[OF s sr up vp tr line comp endpoint_proportional])
 have positive: "0<f1" using f1 by arith
 have gcd: "1<gcd u v" by (rule proportional_lattice_point_gcd_gt_one[OF positive conjunct1[OF proper] endpoint_proportional])
 show ?thesis using proper gcd by blast
qed

lemma homogeneous_unit_defect_endpoint_impossible:
 fixes R F::"complex bivariate" and rho s u::nat and q::int
 assumes s: "0<s" and direction: "is_direction (int rho) (-int s)" and q: "0<q"
 and Rhom: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=q"
 and Fhom: "\<And>d. d\<in>biv_support F \<Longrightarrow> pair_weight (int rho) (-int s) d=int rho-int s"
 and endpt: "(u,u+1)\<in>biv_support R"
 and max: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 and card: "1<card(biv_support R)" and companion: "biv_poisson R F=R"
 shows False
proof -
 have Rnz: "R\<noteq>0" using endpt by auto
 have nonempty: "biv_support R\<noteq>{}" using Rnz by simp
 have minimum: "Min(fst ` biv_support R)\<in>fst ` biv_support R"
   by (rule Min_in) (use nonempty in auto)
 obtain r t where start: "(r,t)\<in>biv_support R" and minimum: "r=Min(fst ` biv_support R)"
   using minimum by (metis imageE prod.collapse)
 have min: "r\<le>fst d" if "d\<in>biv_support R" for d
   unfolding minimum by (rule Min_le) (use that in auto)
 have ru: "r<u"
 proof -
   have le: "r\<le>u" using max[OF start] by simp
   have unequal: "r\<noteq>u"
   proof
     assume eq: "r=u"
     have unique: "d=(u,u+1)" if d: "d\<in>biv_support R" for d
     proof -
       have x: "fst d=u" using min[OF d] max[OF d] eq by arith
       show ?thesis by (rule homogeneous_max_x_unique[OF s Rhom endpt d x])
     qed
     have subset: "biv_support R\<subseteq>{(u,u+1)}" using unique by blast
     have "card(biv_support R)\<le>1" using card_mono[OF _ subset] by simp
     then show False using card by arith
   qed
   show ?thesis using le unequal by arith
 qed
 have sr: "s<rho" using direction by (simp add: is_direction_def)
 have sz: "0<int s" using s by simp
 have sum: "0<int rho-int s" using sr by simp
 have delta: "0<int u-int r" using ru by simp
 have product: "0<(int rho-int s)*(int u-int r)" by (rule mult_pos_pos[OF sum delta])
 have endweight: "int rho*int u-int s*(int u+1)=q"
   using Rhom[OF endpt] by (simp add: pair_weight_def mult.commute add.commute)
 have startweight: "int rho*int r-int s*int t=q"
   using Rhom[OF start] by (simp add: pair_weight_def mult.commute add.commute)
 have line: "int s*(int r-int t+1)=(int rho-int s)*(int u-int r)"
   using endweight startweight by (simp add: algebra_simps; arith)
 have product_start: "0<int s*(int r-int t+1)" using product line by simp
 have sign: "0<int r-int t+1" using product_start sz by (simp add: zero_less_mult_iff; arith)
 have start_nonnegative: "0\<le>int r-int t" using sign by arith
 have grade_max: "pair_grade d\<le>pair_grade (r,t)" if d: "d\<in>biv_support R" for d
 proof -
   have dw: "int rho*int(fst d)-int s*int(snd d)=q"
     using Rhom[OF d] by (simp add: pair_weight_def mult.commute add.commute)
   have difference: "int s*((int r-int t)-(int(fst d)-int(snd d)))=
     (int rho-int s)*(int(fst d)-int r)"
     using dw startweight by (simp add: algebra_simps; arith)
   have nonnegative: "0\<le>(int rho-int s)*(int(fst d)-int r)"
     by (rule mult_nonneg_nonneg) (use sum min[OF d] in auto)
   have result: "int(fst d)-int(snd d)\<le>int r-int t"
   proof (rule ccontr)
     assume "\<not>int(fst d)-int(snd d)\<le>int r-int t"
     then have negative: "(int r-int t)-(int(fst d)-int(snd d))<0" by arith
     have "int s*((int r-int t)-(int(fst d)-int(snd d)))<0"
       by (rule mult_pos_neg[OF sz negative])
     then show False using difference nonnegative by arith
   qed
   show ?thesis using result by (simp add: pair_grade_def)
 qed
 have start_positive: "0<pair_grade (r,t)"
 proof (rule ccontr)
   assume "\<not>0<pair_grade (r,t)"
   then have diagonal: "r=t" using start_nonnegative by (simp add: pair_grade_def; arith)
   have rpositive: "0<r"
   proof (rule ccontr)
     assume "\<not>0<r"
     then have zero: "r=0" by simp
     show False using startweight q by (simp add: zero diagonal[symmetric])
   qed
   have nonzero_sum: "int rho+(-int s)\<noteq>0" using sum by simp
   have diag: "fst(r,t)=snd(r,t)" using diagonal by simp
   have pos: "0<fst(r,t)" using rpositive by simp
   show False by (rule poisson_companion_no_diagonal_homogeneous_max[OF nonzero_sum Rhom Fhom companion start grade_max diag pos])
 qed
 have Fnz: "F\<noteq>0" using companion Rnz by (auto simp: biv_poisson_def)
 have Fnonempty: "biv_support F\<noteq>{}" using Fnz by simp
 have maximum: "Max(fst ` biv_support F)\<in>fst ` biv_support F" by (rule Max_in) (use Fnonempty in auto)
 obtain f1 f2 where Fend: "(f1,f2)\<in>biv_support F" and maximum: "f1=Max(fst ` biv_support F)"
   using maximum by (metis imageE prod.collapse)
 have Fmax: "fst d\<le>f1" if "d\<in>biv_support F" for d
   unfolding maximum by (rule Max_ge) (use that in auto)
 have end_negative: "pair_grade(u,u+1)<0" by (simp add: pair_grade_def)
 have bad: "1<gcd u (u+1)"
   using homogeneous_companion_end_nonprimitive[OF s direction Rhom Fhom endpt start max Fend Fmax companion start_positive end_negative] by blast
 show False using bad by simp
qed
end
