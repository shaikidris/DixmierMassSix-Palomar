theory Small_Crossing_Data_Carrier
 imports "Normalized_Companion_Endpoints"
   "Negative_Common_Root_Normalization"
begin

text \<open>Exact data fields of source GGVSmallDegreeCrossingData. Source
proof fields are represented by one predicate on the native data record,
including the minimality and degree transport conditions. This introduces
no existence premise or axiom.\<close>

record ggv_crossing_configuration =
 ggv_left :: "complex poly_operator"
 ggv_right :: "complex poly_operator"
 ggv_rho :: "nat"
 ggv_s :: "nat"
 ggv_d :: "nat"
 ggv_n :: "nat"
 ggv_u :: "nat"
 ggv_v :: "nat"
 ggv_r :: "nat"
 ggv_t :: "nat"
 ggv_h :: "nat"
 ggv_f1 :: "nat"
 ggv_f2 :: "nat"
 ggv_root :: "complex bivariate"
 ggv_companion :: "complex bivariate"
 ggv_nu :: "complex"
 ggv_mu :: "complex"
 ggv_weight :: "int"

definition ggv_small_degree_crossing_data :: "complex poly_operator\<Rightarrow>complex poly_operator\<Rightarrow>ggv_crossing_configuration\<Rightarrow>bool" where
 "ggv_small_degree_crossing_data = (\<lambda>(P::complex poly_operator) (Q::complex poly_operator) (H::ggv_crossing_configuration).
 is_degree_minimal_counterexample_pair (ggv_left H)(ggv_right H) \<and>
 total_degree(ggv_left H)=total_degree P \<and>
 total_degree(ggv_right H)=total_degree Q \<and>
 0<ggv_rho H \<and>
 0<ggv_s H \<and>
 is_direction(int(ggv_rho H))(-int(ggv_s H)) \<and>
 in_direction(int(ggv_rho H))(-int(ggv_s H))(ggv_left H) \<and>
 in_direction(int(ggv_rho H))(-int(ggv_s H))(ggv_right H) \<and>
 1<ggv_d H \<and>
 1<ggv_n H \<and>
 coprime(ggv_d H)(ggv_n H) \<and>
 ggv_root H\<noteq>0 \<and>
 ggv_nu H\<noteq>0 \<and>
 ggv_mu H\<noteq>0 \<and>
 weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(ggv_weight H)(ggv_root H) \<and>
 leading_form(int(ggv_rho H))(-int(ggv_s H))(ggv_left H)=[:[:ggv_nu H:]:]*(ggv_root H)^(ggv_d H) \<and>
 leading_form(int(ggv_rho H))(-int(ggv_s H))(ggv_right H)=[:[:ggv_mu H:]:]*(ggv_root H)^(ggv_n H) \<and>
 v_degree(int(ggv_rho H))(-int(ggv_s H))(ggv_left H)=int(ggv_d H)*ggv_weight H \<and>
 (ggv_u H,ggv_v H)\<in>biv_support(ggv_root H) \<and>
 (ggv_r H,ggv_t H)\<in>biv_support(ggv_root H) \<and>
 (\<forall>e\<in>biv_support(ggv_root H). fst e\<le>ggv_u H) \<and>
 (\<forall>e\<in>biv_support(ggv_root H). ggv_r H\<le>fst e) \<and>
 ggv_t H<ggv_r H \<and>
 ggv_u H<ggv_v H \<and>
 ggv_r H<ggv_u H \<and>
 ggv_u H+ggv_v H\<le>15 \<and>
 weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(int(ggv_rho H)-int(ggv_s H))(ggv_companion H) \<and>
 biv_poisson(ggv_root H)(ggv_companion H)=ggv_root H \<and>
 (1,1)\<in>biv_support(ggv_companion H) \<and>
 (ggv_f1 H,ggv_f2 H)\<in>biv_support(ggv_companion H) \<and>
 (\<forall>e\<in>biv_support(ggv_companion H). fst e\<le>ggv_f1 H) \<and>
 2\<le>ggv_f1 H \<and>
 ggv_f1 H*ggv_v H=ggv_f2 H*ggv_u H \<and>
 gcd(ggv_f1 H-1)(ggv_f2 H-1)=1 \<and>
 2\<le>ggv_h H \<and>
 ggv_t H\<le>ggv_h H \<and>
 ggv_v H=ggv_t H+ggv_rho H*ggv_h H \<and>
 ggv_rho H*ggv_r H+(ggv_h H-ggv_t H)*ggv_s H=ggv_rho H*ggv_h H-1)"

end
