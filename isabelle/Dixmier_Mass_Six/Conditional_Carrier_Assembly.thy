theory Conditional_Carrier_Assembly
  imports Carrier_Mass_Transport "Shared_Coefficient_Carrier"
begin

text \<open>This is a conditional assembly adapter. The countable embedding and
complex generation premises are explicit assumptions of this adapter; the final
generation theorem discharges them with proved results.\<close>

theorem conditional_carrier_mass_six_generation:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes embedding_gate: "\<And>E :: 'k set.
      division_subring_on E \<Longrightarrow> countable E \<Longrightarrow>
      \<exists>f :: 'k \<Rightarrow> complex. dixmier_carrier_field_embedding E f"
    and complex_generation: "\<And>A B :: complex poly_operator.
      A \<in> weyl_algebra \<Longrightarrow> B \<in> weyl_algebra \<Longrightarrow>
      op_comp B A - op_comp A B = id \<Longrightarrow> weyl_mass A \<le> 6 \<Longrightarrow>
      op_adjoin {A,B} = weyl_algebra"
    and P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and comm: "op_comp Q P - op_comp P Q = id"
    and mass: "weyl_mass P \<le> 6"
  shows "op_adjoin {P,Q} = weyl_algebra"
proof -
  obtain E where closed: "division_subring_on E" and count: "countable E"
    and coeff: "\<forall>a b. pbw_coeff P a b \<in> E \<and> pbw_coeff Q a b \<in> E"
    using exists_countable_pbw_coefficient_carrier[OF P Q] by blast
  obtain f :: "'k \<Rightarrow> complex" where emb: "dixmier_carrier_field_embedding E f"
    using embedding_gate[OF closed count] by blast
  interpret carrier: dixmier_carrier_char_zero_embedding E f
    unfolding dixmier_carrier_char_zero_embedding_def by (rule emb)
  have pe: "P \<in> carrier_weyl E" using P coeff unfolding carrier_weyl_def by blast
  have qe: "Q \<in> carrier_weyl E" using Q coeff unfolding carrier_weyl_def by blast
  show ?thesis
    by (rule carrier.carrier_mass_six_generation_transfer[OF pe qe comm mass complex_generation])
qed

end
