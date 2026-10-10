theory Ramified_Corner_Grade_Barrier
 imports Ramified_Origin_Stripping
   "Ramified_Exact_Weight_Lower"
begin

lemma ramified_corner_top_weights_below_steps:
 fixes l rho sigma d n h wP wQ::int
 assumes l: "0<l" and sum: "0<rho+sigma" and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and positive: "0<wP" and corner: "wP=d*(rho*(l*h-1)+l*sigma*h)"
 and ratio: "wQ*d=wP*n" and step: "wP+wQ=l*(rho+sigma)"
 shows "wP<rho \<and> wQ<rho \<and> wP<l*(rho+sigma) \<and> wQ<l*(rho+sigma)"
proof -
 let ?W="rho*(l*h-1)+l*sigma*h"
 have dp: "0<d" and np: "0<n" using d n by arith+
 have W: "0<?W" using positive corner dp by (simp only: zero_less_mult_iff) auto
 have product: "(wQ-n*?W)*d=0" using corner ratio by algebra
 have Qweight: "wQ=n*?W" using product dp by (simp only: mult_eq_0_iff) auto
 have combined: "l*(rho+sigma)=(d+n)*?W" using corner Qweight step by algebra
 have rho_equation: "rho=(h*(d+n)-1)*?W" using combined by algebra
 have sum_positive: "0\<le>d+n" using d n by arith
 have twice: "2*(d+n)\<le>h*(d+n)" by (rule mult_right_mono[OF h sum_positive])
 have dbound: "d<h*(d+n)-1" and nbound: "n<h*(d+n)-1" using twice d n by arith+
 have Pbelow: "d*?W<(h*(d+n)-1)*?W" by (rule mult_strict_right_mono[OF dbound W])
 have Qbelow: "n*?W<(h*(d+n)-1)*?W" by (rule mult_strict_right_mono[OF nbound W])
 have Qpos: "0<wQ" using Qweight mult_pos_pos[OF np W] by simp
 have Psmall: "wP<rho" using Pbelow corner rho_equation by linarith
 have Qsmall: "wQ<rho" using Qbelow Qweight rho_equation by linarith
 show ?thesis using Psmall Qsmall positive Qpos step by linarith
qed

lemma ramified_nonnegative_nonorigin_weight_lower:
 fixes p::"int\<times>nat"
 assumes rho: "0<rho" and sum: "0<rho+sigma"
 and grade: "0\<le>fst p-int l*int(snd p)" and other: "p\<noteq>(0,0)"
 shows "rho\<le>ramified_weight l rho sigma p \<or> int l*(rho+sigma)\<le>ramified_weight l rho sigma p"
proof (cases "snd p=0")
 case True
 have x: "0<fst p" using grade other True by (auto simp: prod_eq_iff; arith)
 have rho_nonnegative: "0\<le>rho" using rho by arith
 have x_lower: "0\<le>fst p-1" using x by arith
 have product: "0\<le>rho*(fst p-1)" by (rule mult_nonneg_nonneg[OF rho_nonnegative x_lower])
 have normalized_product: "0\<le>rho*fst p-rho"
   using product by (simp only: right_diff_distrib mult_1_right)
 have weighted: "ramified_weight l rho sigma p=rho*fst p"
   using True by (simp add: ramified_weight_def)
 show ?thesis by (rule disjI1)
   (use normalized_product in \<open>simp only: weighted; linarith\<close>)
next
 case False
 have order: "0\<le>int(snd p)-1" using False by arith
 have p1: "0\<le>rho*(fst p-int l*int(snd p))" by (rule mult_nonneg_nonneg) (use rho grade in auto)
 have p2: "0\<le>int l*(int(snd p)-1)" by (rule mult_nonneg_nonneg) (use order in auto)
 have p3: "0\<le>(rho+sigma)*(int l*(int(snd p)-1))" by (rule mult_nonneg_nonneg) (use sum p2 in auto)
 have identity: "ramified_weight l rho sigma p-int l*(rho+sigma)=
   rho*(fst p-int l*int(snd p))+(rho+sigma)*(int l*(int(snd p)-1))"
   unfolding ramified_weight_def by algebra
 show ?thesis by (rule disjI2) (use identity p1 p3 in linarith)
qed

lemma ramified_corner_first_step_nonnegative_only_origin:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and top: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
 and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and first: "fst E=int d*(int h*int l-1)" and second: "snd E=d*h"
 and positive: "0<ramified_weight_deg l rho sigma P"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and step: "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q=int l*(rho+sigma)"
 shows "(\<forall>p\<in>ramified_pbw_support l P. 0\<le>fst p-int l*int(snd p)\<longrightarrow>p=(0,0)) \<and>
   (\<forall>q\<in>ramified_pbw_support l Q. 0\<le>fst q-int l*int(snd q)\<longrightarrow>q=(0,0))"
proof -
 have corner: "ramified_weight_deg l rho sigma P=int d*(rho*(int l*int h-1)+int l*sigma*int h)"
   using top by (simp add: ramified_weight_def first second algebra_simps)
 have bounds: "ramified_weight_deg l rho sigma P<rho \<and> ramified_weight_deg l rho sigma Q<rho \<and>
   ramified_weight_deg l rho sigma P<int l*(rho+sigma) \<and> ramified_weight_deg l rho sigma Q<int l*(rho+sigma)"
   by (rule ramified_corner_top_weights_below_steps[where l="int l" and d="int d" and n="int n" and h="int h", OF _ sum _ _ _ positive corner ratio step])
     (use l d n h in auto)
 have only: "p=(0,0)" if carrier: "T\<in>ramified_operator_algebra l"
   and small: "ramified_weight_deg l rho sigma T<rho" "ramified_weight_deg l rho sigma T<int l*(rho+sigma)"
   and member: "p\<in>ramified_pbw_support l T" and grade: "0\<le>fst p-int l*int(snd p)" for T p
 proof (rule ccontr)
   assume other: "p\<noteq>(0,0)"
   have lower: "rho\<le>ramified_weight l rho sigma p \<or> int l*(rho+sigma)\<le>ramified_weight l rho sigma p"
     by (rule ramified_nonnegative_nonorigin_weight_lower[OF rho sum grade other])
   have upper: "ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
     by (rule ramified_weight_deg_upper[OF member])
   show False using small lower upper by arith
 qed
 show ?thesis using only[OF P] only[OF Q] bounds by blast
qed

lemma ramified_corner_exact_pair_weight_sum_strict:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and top: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
 and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and first: "fst E=int d*(int h*int l-1)" and second: "snd E=d*h"
 and positive: "0<ramified_weight_deg l rho sigma P"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 shows "int l*(rho+sigma)<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q"
proof -
 have lower: "int l*(rho+sigma)\<le>ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q"
   using ramified_exact_pair_weightDeg_sum_lower[OF l rho sum Q P exact] by (simp only: add.commute)
 have unequal: "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q\<noteq>int l*(rho+sigma)"
 proof
   assume equal: "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q=int l*(rho+sigma)"
   have only: "(\<forall>p\<in>ramified_pbw_support l P. 0\<le>fst p-int l*int(snd p)\<longrightarrow>p=(0,0)) \<and>
     (\<forall>q\<in>ramified_pbw_support l Q. 0\<le>fst q-int l*int(snd q)\<longrightarrow>q=(0,0))"
     by (rule ramified_corner_first_step_nonnegative_only_origin[OF l rho sum P Q top d n h first second positive ratio equal])
   show False using only ramified_exact_pair_has_nonorigin_nonnegative_grade_point[OF l P Q exact] by blast
 qed
 show ?thesis using lower unequal by arith
qed

end
