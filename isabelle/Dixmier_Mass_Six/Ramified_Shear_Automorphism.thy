theory Ramified_Shear_Automorphism
  imports Ramified_Shear_Intertwining
begin

lemma laurent_comp_diff_left:
  "laurent_comp (T-U) V = laurent_comp T V - laurent_comp U V"
  by (rule ext) (simp add: laurent_comp_def)

lemma ramified_shear_candidate_zero_operator:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h 0 = 0"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_zero)

lemma ramified_pbw_coeffs_diff:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_pbw_coeffs l (T-U) = ramified_pbw_coeffs l T - ramified_pbw_coeffs l U"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: ramified_algebra_diff ramified_normal_eval_sub ramified_pbw_coeffs_eval)

lemma ramified_shift_eval_diff:
  "ramified_shift_eval l h (a-b) = ramified_shift_eval l h a - ramified_shift_eval l h b"
proof -
  have "ramified_shift_eval l h (a-b) + ramified_shift_eval l h b = ramified_shift_eval l h a"
    using ramified_shift_eval_add[of l h "a-b" b] by simp
  then show ?thesis by (simp add: eq_diff_eq)
qed

lemma ramified_shear_candidate_diff:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (T-U) = ramified_shear_candidate l h T - ramified_shear_candidate l h U"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_diff ramified_shift_eval_diff)

lemma ramified_shear_candidate_one:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h id = id"
  using ramified_shear_candidate_coeff_gen[where f=1]
  by (simp add: ramified_coeff_gen_def ramified_coeff_mul_one)

lemma ramified_shear_candidate_algebra_map:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h (laurent_scalar c) = laurent_scalar c"
  using ramified_shear_candidate_coeff_gen[where f="Poly_Mapping.single 0 c"]
  by (simp add: ramified_coeff_gen_def ramified_coeff_mul_C)

definition ramified_shifted_Y_gen ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator" where
  "ramified_shifted_Y_gen l h = ramified_shifted_Y l h"

lemma ramified_shifted_Y_gen_carrier:
  "ramified_shifted_Y_gen l h \<in> ramified_operator_algebra l"
  by (simp add: ramified_shifted_Y_gen_def ramified_shifted_Y_mem)

lemma ramified_shear_candidate_Y_gen_sub:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h (ramified_Y_gen l) = ramified_shifted_Y_gen l h"
  by (simp add: ramified_shifted_Y_gen_def ramified_shear_candidate_Y_gen)

lemma ramified_shear_candidate_derivative_left_sub:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (laurent_comp (ramified_Y_gen l) T) =
   laurent_comp (ramified_shifted_Y_gen l h) (ramified_shear_candidate l h T)"
  by (simp add: ramified_shifted_Y_gen_def ramified_shear_candidate_derivative_left)

lemma laurent_scalar_comp:
  "laurent_comp (laurent_scalar c) T = normal_smult c T"
  by (simp add: laurent_scalar_def laurent_comp_def normal_smult_def)

lemma ramified_shear_candidate_mul_aux:
  assumes positive: "0 < l" and T: "T \<in> ramified_operator_algebra l"
  shows "\<forall>U\<in>ramified_operator_algebra l.
    ramified_shear_candidate l h (laurent_comp T U) =
    laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h U)"
  using T[unfolded ramified_operator_algebra_def]
proof (induction rule: laurent_adjoin.induct)
  case (generator T)
  show ?case
  proof (intro ballI)
    fix U assume U: "U \<in> ramified_operator_algebra l"
    from generator.hyps consider f where "T = ramified_coeff_mul f" |
      "T = ramified_derivative l" by auto
    then show "ramified_shear_candidate l h (laurent_comp T U) =
      laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h U)"
    proof cases
      case (1 f)
      show ?thesis using ramified_shear_candidate_coeff_left[OF positive U, of h f]
        ramified_shear_candidate_coeff_gen[OF positive, of h f]
        by (simp add: 1 ramified_coeff_gen_def)
    next
      case 2
      show ?thesis using ramified_shear_candidate_derivative_left[OF positive U, of h]
        ramified_shear_candidate_Y_gen[OF positive, of h]
        by (simp add: 2 ramified_Y_gen_def)
    qed
  qed
next
  case (scalar c)
  show ?case
    by (simp add: laurent_scalar_comp ramified_shear_candidate_smult[OF positive]
        ramified_shear_candidate_algebra_map[OF positive])
next
  case (add T U)
  have TM: "T \<in> ramified_operator_algebra l" and UM: "U \<in> ramified_operator_algebra l"
    using add.hyps unfolding ramified_operator_algebra_def by blast+
  show ?case
  proof (intro ballI)
    fix V assume VM: "V \<in> ramified_operator_algebra l"
    have TI: "ramified_shear_candidate l h (laurent_comp T V) =
      laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h V)"
      using add.IH(1) VM by blast
    have UI: "ramified_shear_candidate l h (laurent_comp U V) =
      laurent_comp (ramified_shear_candidate l h U) (ramified_shear_candidate l h V)"
      using add.IH(2) VM by blast
    show "ramified_shear_candidate l h (laurent_comp (T+U) V) =
      laurent_comp (ramified_shear_candidate l h (T+U)) (ramified_shear_candidate l h V)"
      by (simp add: laurent_comp_add_left ramified_shear_candidate_add[OF positive]
          ramified_algebra_comp TM UM VM TI UI)
  qed
next
  case (diff T U)
  have TM: "T \<in> ramified_operator_algebra l" and UM: "U \<in> ramified_operator_algebra l"
    using diff.hyps unfolding ramified_operator_algebra_def by blast+
  show ?case
  proof (intro ballI)
    fix V assume VM: "V \<in> ramified_operator_algebra l"
    have TI: "ramified_shear_candidate l h (laurent_comp T V) =
      laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h V)"
      using diff.IH(1) VM by blast
    have UI: "ramified_shear_candidate l h (laurent_comp U V) =
      laurent_comp (ramified_shear_candidate l h U) (ramified_shear_candidate l h V)"
      using diff.IH(2) VM by blast
    show "ramified_shear_candidate l h (laurent_comp (T-U) V) =
      laurent_comp (ramified_shear_candidate l h (T-U)) (ramified_shear_candidate l h V)"
      by (simp add: laurent_comp_diff_left ramified_shear_candidate_diff[OF positive]
          ramified_algebra_comp TM UM VM TI UI)
  qed
next
  case (comp T U)
  have TM: "T \<in> ramified_operator_algebra l" and UM: "U \<in> ramified_operator_algebra l"
    using comp.hyps unfolding ramified_operator_algebra_def by blast+
  show ?case
  proof (intro ballI)
    fix V assume VM: "V \<in> ramified_operator_algebra l"
    have UV: "laurent_comp U V \<in> ramified_operator_algebra l"
      by (rule ramified_algebra_comp[OF UM VM])
    have TI: "ramified_shear_candidate l h (laurent_comp T (laurent_comp U V)) =
      laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h (laurent_comp U V))"
      using comp.IH(1) UV by blast
    have UI: "ramified_shear_candidate l h (laurent_comp U V) =
      laurent_comp (ramified_shear_candidate l h U) (ramified_shear_candidate l h V)"
      using comp.IH(2) VM by blast
    have TU: "ramified_shear_candidate l h (laurent_comp T U) =
      laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h U)"
      using comp.IH(1) UM by blast
    show "ramified_shear_candidate l h (laurent_comp (laurent_comp T U) V) =
      laurent_comp (ramified_shear_candidate l h (laurent_comp T U)) (ramified_shear_candidate l h V)"
      by (simp add: laurent_comp_assoc TI UI TU)
  qed
qed

theorem ramified_shear_candidate_mul:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (laurent_comp T U) =
   laurent_comp (ramified_shear_candidate l h T) (ramified_shear_candidate l h U)"
  using ramified_shear_candidate_mul_aux by blast

definition ramified_alg_hom_on ::
  "nat \<Rightarrow> (laurent_operator \<Rightarrow> laurent_operator) \<Rightarrow> bool" where
  "ramified_alg_hom_on l F \<longleftrightarrow>
    (\<forall>T\<in>ramified_operator_algebra l. F T \<in> ramified_operator_algebra l) \<and>
    (\<forall>c. F (laurent_scalar c) = laurent_scalar c) \<and>
    (\<forall>T\<in>ramified_operator_algebra l. \<forall>U\<in>ramified_operator_algebra l.
      F (T+U) = F T + F U \<and> F (T-U) = F T - F U \<and>
      F (laurent_comp T U) = laurent_comp (F T) (F U))"

definition ramified_shear_hom ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "ramified_shear_hom l h = ramified_shear_candidate l h"

lemma ramified_shear_hom_carrier:
  "0 < l \<Longrightarrow> ramified_alg_hom_on l (ramified_shear_hom l h)"
  by (auto simp: ramified_alg_hom_on_def ramified_shear_hom_def
      intro: ramified_shear_candidate_mem ramified_shear_candidate_algebra_map
      ramified_shear_candidate_add ramified_shear_candidate_diff ramified_shear_candidate_mul)

lemma ramified_alg_hom_ext:
  assumes F: "ramified_alg_hom_on l F" and G: "ramified_alg_hom_on l G"
    and coeff: "\<And>f. F (ramified_coeff_gen l f) = G (ramified_coeff_gen l f)"
    and Y: "F (ramified_Y_gen l) = G (ramified_Y_gen l)"
    and T: "T \<in> ramified_operator_algebra l"
  shows "F T = G T"
  using T[unfolded ramified_operator_algebra_def]
  by (induction rule: laurent_adjoin.induct)
     (use F G coeff Y in \<open>auto simp only: ramified_alg_hom_on_def
       ramified_operator_algebra_def ramified_coeff_gen_def ramified_Y_gen_def\<close>)

lemma ramified_shifted_Y_gen_eq_add:
  "ramified_shifted_Y_gen l h = ramified_Y_gen l + ramified_coeff_gen l h"
  by (simp add: ramified_shifted_Y_gen_def ramified_shifted_Y_def ramified_Y_gen_def ramified_coeff_gen_def)

lemma ramified_coeff_gen_neg:
  "ramified_coeff_gen l (-h) = -ramified_coeff_gen l h"
  by (rule ext) (simp add: ramified_coeff_gen_def ramified_coeff_mul_def)

lemma ramified_shear_hom_inverse_on_Y:
  assumes positive: "0 < l"
  shows "ramified_shear_hom l (-h) (ramified_shear_hom l h (ramified_Y_gen l)) =
   ramified_Y_gen l"
proof -
  have YM: "ramified_Y_gen l \<in> ramified_operator_algebra l"
    by (simp add: ramified_Y_gen_def derivative_mem_ramified_operator_algebra)
  have CM: "ramified_coeff_gen l h \<in> ramified_operator_algebra l"
    by (simp add: ramified_coeff_gen_def coeff_mem_ramified_operator_algebra)
  show ?thesis
    unfolding ramified_shear_hom_def
    by (simp only: ramified_shear_candidate_Y_gen_sub[OF positive]
        ramified_shifted_Y_gen_eq_add ramified_shear_candidate_add[OF positive YM CM]
        ramified_shear_candidate_coeff_gen[OF positive] ramified_coeff_gen_neg)
       simp
qed

lemma ramified_alg_hom_comp:
  "ramified_alg_hom_on l F \<Longrightarrow> ramified_alg_hom_on l G \<Longrightarrow>
   ramified_alg_hom_on l (F \<circ> G)"
  by (auto simp: ramified_alg_hom_on_def)

lemma ramified_alg_hom_id: "ramified_alg_hom_on l id"
  by (simp add: ramified_alg_hom_on_def)

lemma ramified_shear_hom_inverse_left:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
  shows "ramified_shear_hom l (-h) (ramified_shear_hom l h T) = T"
proof -
  have "((ramified_shear_hom l (-h)) \<circ> ramified_shear_hom l h) T = id T"
  proof (rule ramified_alg_hom_ext[
      where F="ramified_shear_hom l (-h) \<circ> ramified_shear_hom l h" and G=id and l=l])
    show "ramified_alg_hom_on l (ramified_shear_hom l (-h) \<circ> ramified_shear_hom l h)"
      by (intro ramified_alg_hom_comp ramified_shear_hom_carrier assms(1))
    show "ramified_alg_hom_on l id" by (rule ramified_alg_hom_id)
    show "\<And>f. (ramified_shear_hom l (-h) \<circ> ramified_shear_hom l h) (ramified_coeff_gen l f) =
        id (ramified_coeff_gen l f)"
      by (simp only: comp_apply id_apply ramified_shear_hom_def
          ramified_shear_candidate_coeff_gen[OF assms(1)])
    show "(ramified_shear_hom l (-h) \<circ> ramified_shear_hom l h) (ramified_Y_gen l) =
        id (ramified_Y_gen l)"
      using ramified_shear_hom_inverse_on_Y[OF assms(1)] by simp
    show "T \<in> ramified_operator_algebra l" by (rule assms(2))
  qed
  then show ?thesis by simp
qed

lemma ramified_shear_hom_inverse_right:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_hom l h (ramified_shear_hom l (-h) T) = T"
  using ramified_shear_hom_inverse_left[where h="-h"] by simp

definition ramified_alg_aut_on ::
  "nat \<Rightarrow> (laurent_operator \<Rightarrow> laurent_operator) \<Rightarrow>
    (laurent_operator \<Rightarrow> laurent_operator) \<Rightarrow> bool" where
  "ramified_alg_aut_on l F G \<longleftrightarrow>
    ramified_alg_hom_on l F \<and> ramified_alg_hom_on l G \<and>
    (\<forall>T\<in>ramified_operator_algebra l. G (F T) = T \<and> F (G T) = T)"

definition ramified_shear_aut ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow>
    (laurent_operator \<Rightarrow> laurent_operator) \<times> (laurent_operator \<Rightarrow> laurent_operator)" where
  "ramified_shear_aut l h = (ramified_shear_hom l h, ramified_shear_hom l (-h))"

theorem ramified_shear_aut_carrier:
  "0 < l \<Longrightarrow> ramified_alg_aut_on l (fst (ramified_shear_aut l h)) (snd (ramified_shear_aut l h))"
  by (simp add: ramified_shear_aut_def ramified_alg_aut_on_def ramified_shear_hom_carrier
      ramified_shear_hom_inverse_left ramified_shear_hom_inverse_right)
end
