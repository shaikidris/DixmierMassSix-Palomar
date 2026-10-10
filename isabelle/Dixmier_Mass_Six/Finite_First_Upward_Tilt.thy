theory Finite_First_Upward_Tilt
 imports "HOL.Rat"
begin

text \<open>Exact finite minimum-gap architecture of GGVFaceFirstTilt.lean at
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

lemma finiteSupport_exists_first_upward_tilt:
 fixes S::"'a set" and y::"'a\<Rightarrow>nat" and w::"'a\<Rightarrow>rat" and V::rat and M::nat
 assumes finite: "finite S" and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
   and endpt: "\<And>p. p\<in>S \<Longrightarrow> w p=V \<Longrightarrow> y p\<le>M"
   and above: "\<exists>p\<in>S. M<y p"
 shows "\<exists>t::rat. 0<t \<and> (\<forall>p\<in>S. w p+t*of_nat(y p)\<le>V+t*of_nat M) \<and>
   (\<exists>B\<in>S. M<y B \<and> w B+t*of_nat(y B)=V+t*of_nat M)"
proof -
 let ?L="{p\<in>S. M<y p}"
 let ?gap="\<lambda>p. (V-w p)/(of_nat(y p)-of_nat M)"
 let ?values="?gap ` ?L"
 have Lfinite: "finite ?L" using finite by simp
 have nonempty: "?L\<noteq>{}" using above by blast
 have gap_positive: "0<?gap p" if p: "p\<in>?L" for p
 proof -
   have member: "p\<in>S" and higher: "M<y p" using p by auto
   have strict: "w p<V" using top[OF member] endpt[OF member] higher by fastforce
   have denominator: "(0::rat)<of_nat(y p)-of_nat M" using higher by simp
   show ?thesis by (rule divide_pos_pos) (use strict denominator in simp_all)
 qed
 have finite_values: "finite ?values" using Lfinite by simp
 have values_nonempty: "?values\<noteq>{}" using nonempty by simp
 have minimum: "Min ?values\<in>?values" by (rule Min_in[OF finite_values values_nonempty])
 obtain B where image_eq: "Min ?values=?gap B" and B: "B\<in>?L"
   using minimum by (rule imageE)
 have minimum_B: "?gap B=Min ?values" by (rule sym[OF image_eq])
 let ?t="Min ?values"
 have positive: "0<?t" using gap_positive[OF B] by (simp only: minimum_B)
 have bound: "w p+?t*of_nat(y p)\<le>V+?t*of_nat M" if p: "p\<in>S" for p
 proof (cases "M<y p")
   case True
   have member: "p\<in>?L" using p True by simp
   have image_member: "?gap p\<in>?values" by (rule imageI[OF member])
   have least: "?t\<le>?gap p" by (rule Min_le[OF finite_values image_member])
   have denominator: "(0::rat)<of_nat(y p)-of_nat M" using True by simp
   have product: "?t*(of_nat(y p)-of_nat M)\<le>V-w p"
     using least by (simp only: pos_le_divide_eq[OF denominator])
   show ?thesis using product by (simp add: algebra_simps)
 next
   case False
   have order: "(of_nat(y p)::rat)\<le>of_nat M" using False by simp
   have multiply: "?t*of_nat(y p)\<le>?t*of_nat M"
     by (rule mult_left_mono[OF order]) (use positive in simp)
   show ?thesis using top[OF p] multiply by arith
 qed
 have Bmember: "B\<in>S" and higher: "M<y B" using B by auto
 have denominator: "(of_nat(y B)::rat)-of_nat M\<noteq>0" using higher by simp
 have product: "V-w B=?t*(of_nat(y B)-of_nat M)"
   using minimum_B by (simp only: nonzero_divide_eq_eq[OF denominator])
 have tie: "w B+?t*of_nat(y B)=V+?t*of_nat M" using product by algebra
 show ?thesis by (intro exI[of _ ?t]) (use positive bound Bmember higher tie in blast)
qed

lemma finiteSupport_before_upward_tilt_old_endpoint:
 fixes S::"'a set" and y::"'a\<Rightarrow>nat" and w::"'a\<Rightarrow>rat" and V u tFirst::rat and M::nat
 assumes positive: "0<u" and before: "u<tFirst"
   and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
   and first: "\<And>p. p\<in>S \<Longrightarrow> w p+tFirst*of_nat(y p)\<le>V+tFirst*of_nat M"
   and p: "p\<in>S" and tie: "w p+u*of_nat(y p)=V+u*of_nat M"
 shows "y p=M \<and> w p=V"
proof -
 have lower: "(of_nat M::rat)\<le>of_nat(y p)"
 proof (rule ccontr)
   assume bad: "\<not>(of_nat M::rat)\<le>of_nat(y p)"
   have product: "0<u*(of_nat M-of_nat(y p))" by (rule mult_pos_pos) (use positive bad in auto)
   show False using top[OF p] tie product by (simp add: algebra_simps; arith)
 qed
 have upper: "(of_nat(y p)::rat)\<le>of_nat M"
 proof (rule ccontr)
   assume bad: "\<not>(of_nat(y p)::rat)\<le>of_nat M"
   have product: "0<(tFirst-u)*(of_nat(y p)-of_nat M)"
     by (rule mult_pos_pos) (use before bad in auto)
   show False using first[OF p] tie product by (simp add: algebra_simps; arith)
 qed
 have equal: "y p=M" using lower upper by simp
 show ?thesis using equal tie by simp
qed

lemma finiteSupport_first_upward_tilt_le_later:
 fixes S::"'a set" and y::"'a\<Rightarrow>nat" and w::"'a\<Rightarrow>rat" and V tFirst tLater::rat and M::nat
 assumes first: "\<And>p. p\<in>S \<Longrightarrow> w p+tFirst*of_nat(y p)\<le>V+tFirst*of_nat M"
   and b: "b\<in>S" and higher: "M<y b"
   and later: "V+tLater*of_nat M\<le>w b+tLater*of_nat(y b)"
 shows "tFirst\<le>tLater"
proof (rule ccontr)
 assume bad: "\<not>tFirst\<le>tLater"
 have product: "0<(tFirst-tLater)*(of_nat(y b)-of_nat M)"
   by (rule mult_pos_pos) (use bad higher in auto)
 show False using first[OF b] later product by (simp add: algebra_simps; arith)
qed

end
