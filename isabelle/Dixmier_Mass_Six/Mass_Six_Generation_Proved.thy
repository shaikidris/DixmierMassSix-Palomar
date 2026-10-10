theory Mass_Six_Generation_Proved
 imports "Complex_Generation"
   "GGV_Inputs_Proved"
   "Carrier_Mass_Reduction"
begin

theorem massSixGeneration_complex:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and comm: "op_comp Q P-op_comp P Q=id" and mass: "weyl_mass P\<le>6"
 shows "op_adjoin {P,Q}=weyl_algebra"
 by (rule massSixGeneration_complex_of_GGV[OF ggvInputs_proved P Q comm mass])

lemma massSixGeneration_of_GGV:
 fixes P Q::"'k::field_char_0 poly_operator"
 assumes inputs: GGVInputs and P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and comm: "op_comp Q P-op_comp P Q=id" and mass: "weyl_mass P\<le>6"
 shows "op_adjoin {P,Q}=weyl_algebra"
 by (rule mass_six_generation_from_complex[OF massSixGeneration_complex_of_GGV[OF inputs] P Q comm mass])

lemma massSixGeneration_of_degree_bound:
 fixes P Q::"'k::field_char_0 poly_operator"
 assumes degree: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 15<gcd(total_degree R)(total_degree S)"
 and P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and comm: "op_comp Q P-op_comp P Q=id" and mass: "weyl_mass P\<le>6"
 shows "op_adjoin {P,Q}=weyl_algebra"
 by (rule massSixGeneration_of_GGV[OF ggvInputs_of_degree_bound[OF degree] P Q comm mass])

theorem massSixGeneration:
 fixes P Q::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and comm: "op_comp Q P-op_comp P Q=id" and mass: "weyl_mass P\<le>6"
 shows "op_adjoin {P,Q}=weyl_algebra"
 by (rule massSixGeneration_of_degree_bound[OF ggv_degree_bound_proved P Q comm mass])

end
