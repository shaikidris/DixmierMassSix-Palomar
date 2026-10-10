theory Finite_Support_Adjacent_Slope
  imports Polynomial_Cut_Mate_Alignment
begin

lemma finiteSupport_exists_adjacent_rational_slope:
  fixes S :: "(int\<times>nat) set" and w :: "int\<times>nat \<Rightarrow> int" and V :: int and M :: nat
  assumes finite: "finite S" and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> w p=V \<Longrightarrow> M\<le>snd p"
    and below: "\<exists>p\<in>S. snd p<M"
  shows "\<exists>t::rat. 0<t \<and>
    (\<forall>p\<in>S. of_int(w p)-t*of_nat(snd p)\<le>of_int V-t*of_nat M) \<and>
    (\<exists>B\<in>S. snd B<M \<and> of_int(w B)-t*of_nat(snd B)=of_int V-t*of_nat M)"
proof -
  let ?L = "{p\<in>S. snd p<M}"
  let ?gap = "\<lambda>p. (of_int V-of_int(w p))/(of_nat M-of_nat(snd p))::rat"
  let ?values = "?gap ` ?L"
  have Lfinite: "finite ?L" using finite by simp
  have Lnonempty: "?L\<noteq>{}" using below by blast
  have fin: "finite ?values" using Lfinite by simp
  have nonempty: "?values\<noteq>{}" using Lnonempty by simp
  let ?t = "Min ?values"
  obtain B where B: "B\<in>?L" and selected: "?gap B=?t"
    using Min_in[OF fin nonempty] by auto
  have gap_positive: "\<And>p. p\<in>?L \<Longrightarrow> 0<?gap p"
  proof -
    fix p assume p: "p\<in>?L"
    have member: "p\<in>S" and order: "snd p<M" using p by auto
    have strict: "w p<V" using top[OF member] first[OF member] order by arith
    have numerator: "(0::rat)<of_int V-of_int(w p)" using strict by simp
    have denominator: "(0::rat)<of_nat M-of_nat(snd p)" using order by simp
    show "0<?gap p" by (rule divide_pos_pos[OF numerator denominator])
  qed
  have positive: "0<?t" using gap_positive[OF B] selected by simp
  have bounded: "\<forall>p\<in>S. of_int(w p)-?t*of_nat(snd p)\<le>of_int V-?t*of_nat M"
  proof (intro ballI)
    fix p assume member: "p\<in>S"
    show "of_int(w p)-?t*of_nat(snd p)\<le>of_int V-?t*of_nat M"
    proof (cases "snd p<M")
      case True
      have gap_member: "?gap p\<in>?values" using member True by auto
      have minimum: "?t\<le>?gap p" by (rule Min_le[OF fin gap_member])
      have denominator: "(0::rat)<of_nat M-of_nat(snd p)" using True by simp
      have product: "?t*(of_nat M-of_nat(snd p))\<le>of_int V-of_int(w p)"
        using minimum denominator by (simp only: le_divide_eq; auto)
      show ?thesis using product by (simp only: right_diff_distrib; linarith)
    next
      case False
      have order: "(of_nat M::rat)\<le>of_nat(snd p)" using False by simp
      have weight: "(of_int(w p)::rat)\<le>of_int V" using top[OF member] by simp
      have product: "?t*of_nat M\<le>?t*of_nat(snd p)"
        by (rule mult_left_mono[OF order]) (use positive in arith)
      show ?thesis using weight product by linarith
    qed
  qed
  have Bmember: "B\<in>S" and Border: "snd B<M" using B by auto
  have denominator: "(of_nat M-of_nat(snd B)::rat)\<noteq>0" using Border by simp
  have product: "of_int V-of_int(w B)=?t*(of_nat M-of_nat(snd B))"
    using selected denominator by (simp add: nonzero_divide_eq_eq)
  have tie: "of_int(w B)-?t*of_nat(snd B)=of_int V-?t*of_nat M"
    using product by (simp only: right_diff_distrib; linarith)
  show ?thesis using positive bounded Bmember Border tie by blast
qed

lemma finiteSupport_tilted_face_order_le_old_start:
  fixes S :: "(int\<times>nat) set" and w :: "int\<times>nat \<Rightarrow> int" and V :: int and M :: nat and t :: rat
  assumes positive: "0<t" and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
    and member: "p\<in>S"
    and tie: "of_int(w p)-t*of_nat(snd p)=of_int V-t*of_nat M"
  shows "snd p\<le>M"
proof (rule ccontr)
  assume bad: "\<not>snd p\<le>M"
  have order: "(of_nat M::rat)<of_nat(snd p)" using bad by simp
  have product: "t*of_nat M<t*of_nat(snd p)" by (rule mult_strict_left_mono[OF order positive])
  have weight: "(of_int(w p)::rat)\<le>of_int V" using top[OF member] by simp
  show False using product tie weight by linarith
qed

lemma finiteSupport_before_first_slope_bound:
  fixes S :: "(int\<times>nat) set" and w :: "int\<times>nat \<Rightarrow> int" and V :: int and M :: nat and t tFirst :: rat
  assumes positive: "0\<le>t" and before: "t\<le>tFirst"
    and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(w p)-tFirst*of_nat(snd p)\<le>of_int V-tFirst*of_nat M"
  shows "\<forall>p\<in>S. of_int(w p)-t*of_nat(snd p)\<le>of_int V-t*of_nat M"
proof (intro ballI)
  fix p assume p: "p\<in>S"
  have weight: "(of_int(w p)::rat)\<le>of_int V" using top[OF p] by simp
  show "of_int(w p)-t*of_nat(snd p)\<le>of_int V-t*of_nat M"
  proof (cases "snd p\<le>M")
    case True
    have nonnegative: "(0::rat)\<le>of_nat M-of_nat(snd p)" using True by simp
    have gap: "0\<le>(tFirst-t)*(of_nat M-of_nat(snd p))"
      by (rule mult_nonneg_nonneg) (use before nonnegative in auto)
    have expanded: "0\<le>tFirst*of_nat M-tFirst*of_nat(snd p)-t*of_nat M+t*of_nat(snd p)"
      using gap by (simp add: algebra_simps)
    show ?thesis using first[OF p] expanded by linarith
  next
    case False
    have order: "(of_nat M::rat)\<le>of_nat(snd p)" using False by simp
    have product: "t*of_nat M\<le>t*of_nat(snd p)" by (rule mult_left_mono[OF order positive])
    show ?thesis using weight product by linarith
  qed
qed

lemma finiteSupport_before_first_slope_old_endpoint:
  fixes S :: "(int\<times>nat) set" and w :: "int\<times>nat \<Rightarrow> int" and V :: int and M :: nat and t tFirst :: rat
  assumes positive: "0<t" and before: "t<tFirst"
    and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(w p)-tFirst*of_nat(snd p)\<le>of_int V-tFirst*of_nat M"
    and member: "p\<in>S"
    and tie: "of_int(w p)-t*of_nat(snd p)=of_int V-t*of_nat M"
  shows "snd p=M \<and> w p=V"
proof -
  have order: "snd p\<le>M"
    by (rule finiteSupport_tilted_face_order_le_old_start[where S=S and w=w and V=V and M=M and t=t and p=p, OF positive top member tie])
  have equal: "snd p=M"
  proof (rule ccontr)
    assume different: "snd p\<noteq>M"
    have strict: "(of_nat(snd p)::rat)<of_nat M" using order different by simp
    have denominator: "(0::rat)<of_nat M-of_nat(snd p)" using strict by arith
    have product: "t*(of_nat M-of_nat(snd p))<tFirst*(of_nat M-of_nat(snd p))"
      by (rule mult_strict_right_mono[OF before denominator])
    have expanded: "t*of_nat M-t*of_nat(snd p)<tFirst*of_nat M-tFirst*of_nat(snd p)"
      using product by (simp only: right_diff_distrib)
    show False using expanded tie first[OF member] by linarith
  qed
  have weight: "(of_int(w p)::rat)=of_int V" using tie equal by simp
  show ?thesis using equal weight by simp
qed

lemma finiteSupport_first_slope_lt_of_later_exceedance:
  fixes S :: "(int\<times>nat) set" and w :: "int\<times>nat \<Rightarrow> int" and V :: int and M :: nat
    and tFirst tLater :: rat
  assumes later: "0<tLater" and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(w p)-tFirst*of_nat(snd p)\<le>of_int V-tFirst*of_nat M"
    and member: "B\<in>S"
    and exceeds: "of_int V-tLater*of_nat M<of_int(w B)-tLater*of_nat(snd B)"
  shows "tFirst<tLater"
proof -
  have weight: "(of_int(w B)::rat)\<le>of_int V" using top[OF member] by simp
  have order: "snd B<M"
  proof (rule ccontr)
    assume bad: "\<not>snd B<M"
    have order: "(of_nat M::rat)\<le>of_nat(snd B)" using bad by simp
    have product: "tLater*of_nat M\<le>tLater*of_nat(snd B)"
      by (rule mult_left_mono[OF order]) (use later in arith)
    show False using product weight exceeds by linarith
  qed
  have denominator: "(0::rat)<of_nat M-of_nat(snd B)" using order by simp
  show ?thesis
  proof (rule ccontr)
    assume bad: "\<not>tFirst<tLater"
    have product: "tLater*(of_nat M-of_nat(snd B))\<le>tFirst*(of_nat M-of_nat(snd B))"
      by (rule mult_right_mono) (use bad denominator in auto)
    have expanded: "tLater*of_nat M-tLater*of_nat(snd B)\<le>tFirst*of_nat M-tFirst*of_nat(snd B)"
      using product by (simp only: right_diff_distrib)
    show False using expanded exceeds first[OF member] by linarith
  qed
qed

lemma ramifiedSupport_before_first_slope_singleton:
  fixes S :: "(int\<times>nat) set" and t tFirst :: rat
  assumes rho: "0<rho" and Eweight: "ramified_weight l rho sigma E=V"
    and positive: "0<t" and before: "t<tFirst"
    and top: "\<And>p. p\<in>S \<Longrightarrow> ramified_weight l rho sigma p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(ramified_weight l rho sigma p)-tFirst*of_nat(snd p)\<le>
      of_int V-tFirst*of_nat(snd E)"
    and member: "p\<in>S"
    and tie: "of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)=of_int V-t*of_nat(snd E)"
  shows "p=E"
proof -
  have order: "snd p=snd E" and weight: "ramified_weight l rho sigma p=V"
    using finiteSupport_before_first_slope_old_endpoint[OF positive before top first member tie] by auto
  have product: "rho*fst p=rho*fst E" using weight Eweight order by (simp only: ramified_weight_def; linarith)
  have first_coordinate: "fst p=fst E" using product rho by simp
  show ?thesis using first_coordinate order by (simp add: prod_eq_iff)
qed

end
