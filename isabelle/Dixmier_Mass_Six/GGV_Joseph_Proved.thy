theory GGV_Joseph_Proved
  imports "Joseph_Initial_Witness"
    "Counterexample_Positive_Weight"
    "Poisson_Two_Bracket_Polynomiality"
begin

definition GGVJosephTwoBracketInput :: bool where
  "GGVJosephTwoBracketInput \<longleftrightarrow>
    (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
      (\<forall>rho sigma. is_direction rho sigma \<longrightarrow>
        (\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
          biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0 \<and>
          biv_poisson (leading_form rho sigma P)
            (biv_poisson (leading_form rho sigma P) (leading_form rho sigma R))=0)))"

definition GGVJosephFixedPointInput :: bool where
  "GGVJosephFixedPointInput \<longleftrightarrow>
    (\<forall>P Q R::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
      R\<in>op_adjoin {P,Q} \<longrightarrow> (\<forall>rho sigma. is_direction rho sigma \<longrightarrow>
        biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0 \<longrightarrow>
        biv_poisson (leading_form rho sigma P)
          (biv_poisson (leading_form rho sigma P) (leading_form rho sigma R))=0 \<longrightarrow>
        (\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and>
          biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P)))"

lemma ggv_joseph_two_bracket_proved: "GGVJosephTwoBracketInput"
  unfolding GGVJosephTwoBracketInput_def
proof (intro allI impI)
  fix P Q :: "complex poly_operator" and rho sigma :: int
  assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
  have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
    using pair by (auto simp: is_counterexample_pair_def)
  have weight: "0<rho+sigma" using direction by (simp add: is_direction_def)
  have degree: "0<v_degree rho sigma P"
    by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
  show "\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0 \<and>
    biv_poisson (leading_form rho sigma P)
      (biv_poisson (leading_form rho sigma P) (leading_form rho sigma R))=0"
    by (rule joseph_two_bracket_exists_of_positive_degree[OF P Q exact weight degree])
qed

lemma ggv_joseph_fixed_point_proved: "GGVJosephFixedPointInput"
  unfolding GGVJosephFixedPointInput_def
proof (intro allI impI)
  fix P Q R :: "complex poly_operator" and rho sigma :: int
  assume pair: "is_counterexample_pair P Q" and adjoin: "R\<in>op_adjoin {P,Q}"
    and direction: "is_direction rho sigma"
    and bracket: "biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0"
    and second: "biv_poisson (leading_form rho sigma P)
      (biv_poisson (leading_form rho sigma P) (leading_form rho sigma R))=0"
  have degree: "0<v_degree rho sigma P"
    by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
  have pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value (v_degree rho sigma P)"
    using degree by (cases "weighted_degree rho sigma (pbw_symbol P)") (auto simp: v_degree_def)
  have nz: "leading_form rho sigma P\<noteq>0"
    unfolding leading_form_def by (rule weighted_top_component_nonzero[OF pd])
  have ph: "weighted_homogeneous rho sigma (v_degree rho sigma P) (leading_form rho sigma P)"
    and rh: "weighted_homogeneous rho sigma (v_degree rho sigma R) (leading_form rho sigma R)"
    unfolding leading_form_def by (rule weighted_component_homogeneous)+
  have weight: "0<rho+sigma" using direction by (simp add: is_direction_def)
  show "\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and>
    biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P"
    by (rule poisson_homogeneous_fixed_point_of_two_brackets[OF ph rh nz degree weight bracket second])
qed

lemma ggv_preliminary_companion_proved:
  "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
    (\<forall>rho sigma. is_direction rho sigma \<longrightarrow> (\<exists>F.
      weighted_homogeneous rho sigma (rho+sigma) F \<and>
      biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P))"
  using ggv_joseph_two_bracket_proved ggv_joseph_fixed_point_proved
  unfolding GGVJosephTwoBracketInput_def GGVJosephFixedPointInput_def by blast

end
