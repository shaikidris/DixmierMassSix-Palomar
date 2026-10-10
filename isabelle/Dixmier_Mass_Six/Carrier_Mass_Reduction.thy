theory Carrier_Mass_Reduction
  imports "Countable_Complex_Embedding"
    "Conditional_Carrier_Assembly"
begin

theorem mass_six_generation_from_complex:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes complex_generation: "\<And>A B :: complex poly_operator.
      A \<in> weyl_algebra \<Longrightarrow> B \<in> weyl_algebra \<Longrightarrow>
      op_comp B A - op_comp A B = id \<Longrightarrow> weyl_mass A \<le> 6 \<Longrightarrow>
      op_adjoin {A,B} = weyl_algebra"
    and P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and comm: "op_comp Q P - op_comp P Q = id"
    and mass: "weyl_mass P \<le> 6"
  shows "op_adjoin {P,Q} = weyl_algebra"
proof (rule conditional_carrier_mass_six_generation[OF _ complex_generation P Q comm mass])
  fix E :: "'k set"
  assume closed: "division_subring_on E" and count: "countable E"
  show "\<exists>f :: 'k \<Rightarrow> complex. dixmier_carrier_field_embedding E f"
    by (rule countable_carrier_embedding_exists[OF closed count])
qed

end
