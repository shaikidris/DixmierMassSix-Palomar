theory Ramified_Cut_Setup
  imports "Ramified_Shear_Automorphism"
begin
lemma ramified_hom_add:
  "ramified_alg_hom_on l F \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   U \<in> ramified_operator_algebra l \<Longrightarrow> F (T+U) = F T + F U"
  unfolding ramified_alg_hom_on_def by blast
lemma ramified_hom_diff:
  "ramified_alg_hom_on l F \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   U \<in> ramified_operator_algebra l \<Longrightarrow> F (T-U) = F T - F U"
  unfolding ramified_alg_hom_on_def by blast
lemma ramified_hom_comp:
  "ramified_alg_hom_on l F \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   U \<in> ramified_operator_algebra l \<Longrightarrow> F (laurent_comp T U) = laurent_comp (F T) (F U)"
  unfolding ramified_alg_hom_on_def by blast
lemma ramified_hom_scalar:
  "ramified_alg_hom_on l F \<Longrightarrow> F (laurent_scalar c) = laurent_scalar c"
  unfolding ramified_alg_hom_on_def by blast
definition ramified_cut_exponent :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "ramified_cut_exponent l rho sigma = (int l div rho) * sigma"
lemma ramified_cut_exponent_weight:
  "rho dvd int l \<Longrightarrow> rho * ramified_cut_exponent l rho sigma = int l * sigma"
  by (simp add: ramified_cut_exponent_def mult.assoc[symmetric] dvd_mult_div_cancel)
definition ramified_cut_shift :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> ramified_laurent" where
  "ramified_cut_shift l rho sigma c = Poly_Mapping.single (ramified_cut_exponent l rho sigma) c"
lemma ramified_cut_shift_scalar_monomial:
  "ramified_cut_shift l rho sigma c =
    laurent_smult c (Poly_Mapping.single (ramified_cut_exponent l rho sigma) 1)"
  by (simp add: ramified_cut_shift_def laurent_smult_def)
definition ramified_cut_aut ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "ramified_cut_aut l rho sigma c = ramified_shear_hom l (ramified_cut_shift l rho sigma c)"
lemma ramified_cut_aut_certificate:
  "0 < l \<Longrightarrow> ramified_alg_aut_on l (ramified_cut_aut l rho sigma c)
    (ramified_shear_hom l (-ramified_cut_shift l rho sigma c))"
  using ramified_shear_aut_carrier
  by (simp add: ramified_cut_aut_def ramified_shear_aut_def)
lemma ramified_cut_aut_coeff:
  "0 < l \<Longrightarrow> ramified_cut_aut l rho sigma c (ramified_coeff_gen l f) = ramified_coeff_gen l f"
  by (simp add: ramified_cut_aut_def ramified_shear_hom_def ramified_shear_candidate_coeff_gen)
lemma ramified_cut_aut_Y:
  "0 < l \<Longrightarrow> ramified_cut_aut l rho sigma c (ramified_Y_gen l) =
    ramified_Y_gen l + ramified_coeff_gen l (ramified_cut_shift l rho sigma c)"
  by (simp add: ramified_cut_aut_def ramified_shear_hom_def
      ramified_shear_candidate_Y_gen_sub ramified_shifted_Y_gen_eq_add)
lemma ramified_cut_aut_exact_pair:
  assumes "0 < l" "P \<in> ramified_operator_algebra l" "Q \<in> ramified_operator_algebra l"
    "laurent_comp Q P - laurent_comp P Q = id"
  shows "laurent_comp (ramified_cut_aut l rho sigma c Q) (ramified_cut_aut l rho sigma c P) -
    laurent_comp (ramified_cut_aut l rho sigma c P) (ramified_cut_aut l rho sigma c Q) = id"
proof -
  have H: "ramified_alg_hom_on l (ramified_cut_aut l rho sigma c)"
    by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier assms(1))
  have "ramified_cut_aut l rho sigma c (laurent_comp Q P - laurent_comp P Q) =
    laurent_comp (ramified_cut_aut l rho sigma c Q) (ramified_cut_aut l rho sigma c P) -
    laurent_comp (ramified_cut_aut l rho sigma c P) (ramified_cut_aut l rho sigma c Q)"
    by (simp only: ramified_hom_diff[OF H ramified_algebra_comp[OF assms(3,2)]
        ramified_algebra_comp[OF assms(2,3)]]
        ramified_hom_comp[OF H assms(3,2)] ramified_hom_comp[OF H assms(2,3)])
  then show ?thesis
    by (simp add: assms(4) ramified_cut_aut_def ramified_shear_hom_def
        ramified_shear_candidate_one assms(1))
qed
lemma ramified_hom_adjoin_image:
  assumes hom: "ramified_alg_hom_on l F" and generators: "G \<subseteq> ramified_operator_algebra l"
    and member: "T \<in> laurent_adjoin G"
  shows "F T \<in> laurent_adjoin (image F G)"
proof -
  from member have "T \<in> ramified_operator_algebra l \<and> F T \<in> laurent_adjoin (image F G)"
    by (induction rule: laurent_adjoin.induct)
       (use generators in \<open>auto simp only: ramified_hom_add[OF hom] ramified_hom_diff[OF hom]
         ramified_hom_comp[OF hom] ramified_hom_scalar[OF hom] ramified_operator_algebra_def
         intro: laurent_adjoin.intros\<close>)
  then show ?thesis by blast
qed
lemma ramified_aut_generates_forward:
  assumes aut: "ramified_alg_aut_on l F H"
    and P: "P \<in> ramified_operator_algebra l" and Q: "Q \<in> ramified_operator_algebra l"
    and generation: "laurent_adjoin {P,Q} = ramified_operator_algebra l"
  shows "laurent_adjoin {F P,F Q} = ramified_operator_algebra l"
proof
  have hom: "ramified_alg_hom_on l F" "ramified_alg_hom_on l H"
    using aut unfolding ramified_alg_aut_on_def by blast+
  show "laurent_adjoin {F P,F Q} \<subseteq> ramified_operator_algebra l"
    by (rule laurent_adjoin_least)
       (use hom(1) P Q in \<open>auto simp only: ramified_alg_hom_on_def
         intro: ramified_operator_algebra_subalgebra\<close>)
  show "ramified_operator_algebra l \<subseteq> laurent_adjoin {F P,F Q}"
  proof
    fix T assume T: "T \<in> ramified_operator_algebra l"
    have HT: "H T \<in> laurent_adjoin {P,Q}"
      using hom(2) T generation unfolding ramified_alg_hom_on_def by blast
    have "F (H T) \<in> laurent_adjoin (image F {P,Q})"
      by (rule ramified_hom_adjoin_image[OF hom(1) _ HT]) (use P Q in auto)
    then show "T \<in> laurent_adjoin {F P,F Q}"
      using aut T unfolding ramified_alg_aut_on_def by simp
  qed
qed
lemma ramified_cut_aut_generates_iff:
  assumes positive: "0 < l" and P: "P \<in> ramified_operator_algebra l"
    and Q: "Q \<in> ramified_operator_algebra l"
  shows "laurent_adjoin {ramified_cut_aut l rho sigma c P, ramified_cut_aut l rho sigma c Q} =
    ramified_operator_algebra l \<longleftrightarrow> laurent_adjoin {P,Q} = ramified_operator_algebra l"
proof -
  let ?F = "ramified_cut_aut l rho sigma c"
  let ?H = "ramified_shear_hom l (-ramified_cut_shift l rho sigma c)"
  have aut: "ramified_alg_aut_on l ?F ?H"
    by (rule ramified_cut_aut_certificate[OF positive])
  have swapped: "ramified_alg_aut_on l ?H ?F"
    using aut unfolding ramified_alg_aut_on_def by blast
  have FP: "?F P \<in> ramified_operator_algebra l" and FQ: "?F Q \<in> ramified_operator_algebra l"
    using aut P Q unfolding ramified_alg_aut_on_def ramified_alg_hom_on_def by blast+
  have inverse: "?H (?F P) = P" "?H (?F Q) = Q"
    using aut P Q unfolding ramified_alg_aut_on_def by blast+
  show ?thesis
    using ramified_aut_generates_forward[OF aut P Q]
      ramified_aut_generates_forward[OF swapped FP FQ]
    by (simp add: inverse) blast
qed
end
