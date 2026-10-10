theory Carrier_Mass_Transport
  imports "Carrier_Ordered_Word_Descent"
    "PBW_Symbol"
begin

context dixmier_carrier_char_zero_embedding
begin

lemma carrier_base_change_pair_support:
  "T \<in> carrier_weyl E \<Longrightarrow> pbw_pair_support (concrete_base_change f T) = pbw_pair_support T"
  unfolding pbw_pair_support_def by (rule carrier_base_change_support)
lemma carrier_base_change_mass:
  assumes T: "T \<in> carrier_weyl E"
  shows "weyl_mass (concrete_base_change f T) = weyl_mass T"
proof -
  have tw: "T \<in> weyl_algebra" by (rule carrier_weyl_in_weyl[OF T])
  have src: "finite (pbw_pair_support T)" by (rule weyl_finite_pbw_pair_support[OF tw])
  have supp: "pbw_pair_support (concrete_base_change f T) = pbw_pair_support T"
    by (rule carrier_base_change_pair_support[OF T])
  have tgt: "finite (pbw_pair_support (concrete_base_change f T))" using src supp by simp
  show ?thesis
    by (simp only: weyl_mass_def pbw_symbol_support_finite[OF tgt] weyl_symbol_support[OF tw] supp)
qed

theorem carrier_mass_six_generation_transfer:
  fixes P Q :: "'k poly_operator"
  assumes P: "P \<in> carrier_weyl E" and Q: "Q \<in> carrier_weyl E"
    and comm: "op_comp Q P - op_comp P Q = id"
    and mass: "weyl_mass P \<le> 6"
    and target_generation: "\<And>A B :: 'l poly_operator.
      A \<in> weyl_algebra \<Longrightarrow> B \<in> weyl_algebra \<Longrightarrow>
      op_comp B A - op_comp A B = id \<Longrightarrow> weyl_mass A \<le> 6 \<Longrightarrow>
      op_adjoin {A,B} = weyl_algebra"
  shows "op_adjoin {P,Q} = weyl_algebra"
proof (rule carrier_pair_generation_descends[OF P Q])
  have pc: "concrete_base_change f P \<in> weyl_algebra"
    by (rule carrier_base_change_in_weyl[OF carrier_weyl_in_weyl[OF P]])
  have qc: "concrete_base_change f Q \<in> weyl_algebra"
    by (rule carrier_base_change_in_weyl[OF carrier_weyl_in_weyl[OF Q]])
  have cc: "op_comp (concrete_base_change f Q) (concrete_base_change f P) -
      op_comp (concrete_base_change f P) (concrete_base_change f Q) = id"
    by (rule carrier_base_change_commutator_one[OF P Q comm])
  have mc: "weyl_mass (concrete_base_change f P) \<le> 6"
    using mass by (simp only: carrier_base_change_mass[OF P])
  show "op_adjoin {concrete_base_change f P, concrete_base_change f Q} = weyl_algebra"
    by (rule target_generation[OF pc qc cc mc])
qed

end
end
