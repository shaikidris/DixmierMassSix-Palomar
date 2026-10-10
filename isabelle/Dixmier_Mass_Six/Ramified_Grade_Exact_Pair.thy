theory Ramified_Grade_Exact_Pair
  imports "Finite_Support_Adjacent_Slope"
begin

lemma LaurentUpper_derivative_pow:
  fixes j::nat
  assumes upper: "laurent_upper f B"
  shows "laurent_upper ((ramified_derivative l ^^ j) f) (B-int l*int j)"
proof (induction j)
  case 0
  show ?case using upper by simp
next
  case (Suc j)
  have step: "laurent_upper (ramified_derivative l ((ramified_derivative l ^^ j) f)) (B-int l*int j-int l)"
    by (rule laurent_upper_derivative[OF Suc.IH])
  show ?case using step by (simp add: funpow.simps(2) algebra_simps)
qed

lemma LaurentUpper_neg_local:
  "laurent_upper f B \<Longrightarrow> laurent_upper (-f) B"
  by (auto simp: laurent_upper_def Poly_Mapping.in_keys_iff)

lemma LaurentUpper_sub_local:
  assumes "laurent_upper f B" "laurent_upper g B"
  shows "laurent_upper (f-g) B"
  by (simp only: diff_conv_add_uminus) (rule laurent_upper_add[OF assms(1) LaurentUpper_neg_local[OF assms(2)]])

lemma ramified_negative_grade_lowers_upper:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and negative: "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow> fst p-int l*int(snd p)<0"
    and upper: "laurent_upper f B"
  shows "laurent_upper (T f) (B-1)"
proof -
  have coefficient: "\<And>j. laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j) (int l*int j-1)"
  proof (unfold laurent_upper_def, intro ballI)
    fix j i assume i: "i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)"
    have member: "(i,j)\<in>ramified_pbw_support l T"
      using i by (simp add: ramified_pbw_support_mem_iff[OF l T] ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
    have "i-int l*int j<0" using negative[OF member] by simp
    then show "i\<le>int l*int j-1" by arith
  qed
  have summands: "\<And>j. laurent_upper
    (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j * (ramified_derivative l ^^ j) f) (B-1)"
  proof -
    fix j
    have derivative: "laurent_upper ((ramified_derivative l ^^ j) f) (B-int l*int j)"
      by (rule LaurentUpper_derivative_pow[where j=j and l=l, OF upper])
    have product: "laurent_upper
      (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j * (ramified_derivative l ^^ j) f)
      ((int l*int j-1)+(B-int l*int j))"
      by (rule laurent_upper_mul[OF coefficient[of j] derivative])
    show "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j *
      (ramified_derivative l ^^ j) f) (B-1)"
      using product by (simp add: algebra_simps)
  qed
  have sum: "laurent_upper (ramified_normal_eval l (ramified_pbw_coeffs l T) f) (B-1)"
    by (simp only: ramified_normal_eval_apply) (rule laurent_upper_finset_sum, simp, rule summands)
  show ?thesis using sum by (simp only: ramified_pbw_coeffs_eval[OF l T])
qed

lemma LaurentUpper_one_not_negative:
  "\<not>laurent_upper (1::ramified_laurent) (-1)"
proof
  assume upper: "laurent_upper (1::ramified_laurent) (-1)"
  have member: "0\<in>Poly_Mapping.keys (1::ramified_laurent)" by simp
  have "(0::int)\<le>-1" using upper member by (simp only: laurent_upper_def; blast)
  then show False by arith
qed

lemma ramified_exact_pair_has_nonnegative_grade_point:
  assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and exact: "laurent_comp Q P-laurent_comp P Q=id"
  shows "(\<exists>p\<in>ramified_pbw_support l P. 0\<le>fst p-int l*int(snd p)) \<or>
    (\<exists>p\<in>ramified_pbw_support l Q. 0\<le>fst p-int l*int(snd p))"
proof (rule ccontr)
  assume none: "\<not>((\<exists>p\<in>ramified_pbw_support l P. 0\<le>fst p-int l*int(snd p)) \<or>
    (\<exists>p\<in>ramified_pbw_support l Q. 0\<le>fst p-int l*int(snd p)))"
  have Pnegative: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> fst p-int l*int(snd p)<0"
    and Qnegative: "\<And>p. p\<in>ramified_pbw_support l Q \<Longrightarrow> fst p-int l*int(snd p)<0"
    using none by auto
  have Pone: "laurent_upper (P 1) (-1)"
    using ramified_negative_grade_lowers_upper[OF l P Pnegative laurent_upper_one] by simp
  have Qone: "laurent_upper (Q 1) (-1)"
    using ramified_negative_grade_lowers_upper[OF l Q Qnegative laurent_upper_one] by simp
  have QPone: "laurent_upper (Q (P 1)) (-2)"
    using ramified_negative_grade_lowers_upper[OF l Q Qnegative Pone] by simp
  have PQone: "laurent_upper (P (Q 1)) (-2)"
    using ramified_negative_grade_lowers_upper[OF l P Pnegative Qone] by simp
  have equation: "Q (P (1::ramified_laurent))-P (Q 1)=1"
    using arg_cong[OF exact, of "\<lambda>T. T (1::ramified_laurent)"] by (simp add: laurent_comp_def)
  have upper: "laurent_upper (1::ramified_laurent) (-2)"
    using LaurentUpper_sub_local[OF QPone PQone] by (simp only: equation)
  have "laurent_upper (1::ramified_laurent) (-1)" by (rule laurent_upper_mono[OF _ upper]) simp
  then show False using LaurentUpper_one_not_negative by blast
qed

lemma ramified_nonnegative_grade_below_old_order:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and weight: "ramified_weight l rho sigma B\<le>ramified_weight l rho sigma E"
    and Enegative: "fst E-int l*int(snd E)<0"
    and Bnonnegative: "0\<le>fst B-int l*int(snd B)"
  shows "snd B<snd E"
proof (rule ccontr)
  assume bad: "\<not>snd B<snd E"
  have order: "0\<le>int(snd B)-int(snd E)" using bad by simp
  have gap: "0<(fst B-int l*int(snd B))-(fst E-int l*int(snd E))"
    using Enegative Bnonnegative by arith
  have first: "0<rho*((fst B-int l*int(snd B))-(fst E-int l*int(snd E)))"
    by (rule mult_pos_pos[OF rho gap])
  have index: "0\<le>int l*(rho+sigma)" using l positive by simp
  have second: "0\<le>(int l*(rho+sigma))*(int(snd B)-int(snd E))"
    by (rule mult_nonneg_nonneg[OF index order])
  have identity: "ramified_weight l rho sigma B-ramified_weight l rho sigma E=
    rho*((fst B-int l*int(snd B))-(fst E-int l*int(snd E)))+
    (int l*(rho+sigma))*(int(snd B)-int(snd E))"
    by (simp add: ramified_weight_def algebra_simps)
  show False using first second weight identity by linarith
qed

lemma ramifiedSupport_first_slope_before_grade_direction:
  fixes S :: "(int\<times>nat) set" and tFirst :: rat
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and Eweight: "ramified_weight l rho sigma E=V"
    and Egrade: "fst E-int l*int(snd E)<0" and Bgrade: "0\<le>fst B-int l*int(snd B)"
    and top: "\<And>p. p\<in>S \<Longrightarrow> ramified_weight l rho sigma p\<le>V"
    and first: "\<And>p. p\<in>S \<Longrightarrow> of_int(ramified_weight l rho sigma p)-tFirst*of_nat(snd p)\<le>
      of_int V-tFirst*of_nat(snd E)"
    and member: "B\<in>S"
  shows "tFirst<of_nat l*of_int(rho+sigma)"
proof -
  let ?later = "of_nat l*of_int(rho+sigma)::rat"
  have later: "0<?later" using l positive by simp
  have identity: "\<And>p. of_int(ramified_weight l rho sigma p)-?later*of_nat(snd p)=
    of_int rho*(of_int(fst p)-of_nat l*of_nat(snd p))"
    by (simp add: ramified_weight_def algebra_simps)
  have Eneg: "(of_int(fst E)-of_nat l*of_nat(snd E)::rat)<0"
  proof -
    have "(of_int(fst E-int l*int(snd E))::rat)<0" using Egrade by (simp only: of_int_less_0_iff)
    then show ?thesis by (simp only: of_int_diff of_int_mult of_int_of_nat_eq)
  qed
  have Bnonneg: "(0::rat)\<le>of_int(fst B)-of_nat l*of_nat(snd B)"
  proof -
    have "(0::rat)\<le>of_int(fst B-int l*int(snd B))" using Bgrade by (simp only: of_int_0_le_iff)
    then show ?thesis by (simp only: of_int_diff of_int_mult of_int_of_nat_eq)
  qed
  have rhoQ: "(0::rat)<of_int rho" using rho by simp
  have Eproduct: "of_int rho*(of_int(fst E)-of_nat l*of_nat(snd E))<(0::rat)"
    by (rule mult_pos_neg[OF rhoQ Eneg])
  have Bproduct: "(0::rat)\<le>of_int rho*(of_int(fst B)-of_nat l*of_nat(snd B))"
    by (rule mult_nonneg_nonneg) (use rhoQ Bnonneg in auto)
  have exceeds: "of_int V-?later*of_nat(snd E)<of_int(ramified_weight l rho sigma B)-?later*of_nat(snd B)"
    using Eproduct Bproduct by (simp only: Eweight[symmetric] identity; linarith)
  show ?thesis by (rule finiteSupport_first_slope_lt_of_later_exceedance[OF later top first member exceeds])
qed

lemma ramifiedSupport_exists_early_adjacent_slope:
  fixes S :: "(int\<times>nat) set"
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma" and finite: "finite S"
    and Eweight: "ramified_weight l rho sigma E=V"
    and Egrade: "fst E-int l*int(snd E)<0" and Bgrade: "0\<le>fst B-int l*int(snd B)"
    and member: "B\<in>S"
    and top: "\<And>p. p\<in>S \<Longrightarrow> ramified_weight l rho sigma p\<le>V"
    and start: "\<And>p. p\<in>S \<Longrightarrow> ramified_weight l rho sigma p=V \<Longrightarrow> snd E\<le>snd p"
  shows "\<exists>t::rat. 0<t \<and> t<of_nat l*of_int(rho+sigma) \<and>
    (\<forall>p\<in>S. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int V-t*of_nat(snd E)) \<and>
    (\<exists>C\<in>S. snd C<snd E \<and> of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int V-t*of_nat(snd E))"
proof -
  have bound: "ramified_weight l rho sigma B\<le>ramified_weight l rho sigma E"
    using top[OF member] by (simp only: Eweight)
  have order: "snd B<snd E" by (rule ramified_nonnegative_grade_below_old_order[OF l rho positive bound Egrade Bgrade])
  obtain t :: rat where t: "0<t" and first: "\<forall>p\<in>S. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>
      of_int V-t*of_nat(snd E)"
    and tied: "\<exists>C\<in>S. snd C<snd E \<and> of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int V-t*of_nat(snd E)"
    using finiteSupport_exists_adjacent_rational_slope[where S=S and w="ramified_weight l rho sigma"
      and V=V and M="snd E", OF finite top start] member order by blast
  have first_bound: "of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>
      of_int V-t*of_nat(snd E)" if p: "p\<in>S" for p
    by (rule bspec[OF first p])
  have before: "t<of_nat l*of_int(rho+sigma)"
    by (rule ramifiedSupport_first_slope_before_grade_direction[where S=S and E=E and B=B and V=V and tFirst=t,
      OF l rho positive Eweight Egrade Bgrade top first_bound member])
  show ?thesis using t before first tied by blast
qed

lemma ramified_exact_pair_exists_early_adjacent_slope:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and exact: "laurent_comp Q P-laurent_comp P Q=id"
    and EPweight: "ramified_weight l rho sigma EP=VP" and EQweight: "ramified_weight l rho sigma EQ=VQ"
    and EPgrade: "fst EP-int l*int(snd EP)<0" and EQgrade: "fst EQ-int l*int(snd EQ)<0"
    and Ptop: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma p\<le>VP"
    and Qtop: "\<And>p. p\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l rho sigma p\<le>VQ"
    and Pstart: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma p=VP \<Longrightarrow> snd EP\<le>snd p"
    and Qstart: "\<And>p. p\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l rho sigma p=VQ \<Longrightarrow> snd EQ\<le>snd p"
  shows "(\<exists>t::rat. 0<t \<and> t<of_nat l*of_int(rho+sigma) \<and>
    (\<forall>p\<in>ramified_pbw_support l P. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd EP)) \<and>
    (\<exists>C\<in>ramified_pbw_support l P. snd C<snd EP \<and> of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int VP-t*of_nat(snd EP))) \<or>
    (\<exists>t::rat. 0<t \<and> t<of_nat l*of_int(rho+sigma) \<and>
    (\<forall>p\<in>ramified_pbw_support l Q. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int VQ-t*of_nat(snd EQ)) \<and>
    (\<exists>C\<in>ramified_pbw_support l Q. snd C<snd EQ \<and> of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int VQ-t*of_nat(snd EQ)))"
proof -
  have alternatives: "(\<exists>B\<in>ramified_pbw_support l P. 0\<le>fst B-int l*int(snd B)) \<or>
    (\<exists>B\<in>ramified_pbw_support l Q. 0\<le>fst B-int l*int(snd B))"
    by (rule ramified_exact_pair_has_nonnegative_grade_point[OF l P Q exact])
  show ?thesis
  proof (cases rule: disjE[OF alternatives])
    case 1
    then obtain B where B: "B\<in>ramified_pbw_support l P" and grade: "0\<le>fst B-int l*int(snd B)" by blast
    show ?thesis by (rule disjI1, rule ramifiedSupport_exists_early_adjacent_slope[
      OF l rho positive ramified_pbw_support_finite EPweight EPgrade grade B Ptop Pstart])
  next
    case 2
    then obtain B where B: "B\<in>ramified_pbw_support l Q" and grade: "0\<le>fst B-int l*int(snd B)" by blast
    show ?thesis by (rule disjI2, rule ramifiedSupport_exists_early_adjacent_slope[
      OF l rho positive ramified_pbw_support_finite EQweight EQgrade grade B Qtop Qstart])
  qed
qed

end
