theory Grade_Projection_Adapters
 imports "Exact_Grade_Projection"
begin

lemma symbol_exact_grade_projection:
 fixes T :: "complex poly_operator"
 assumes T: "T\<in>weyl_algebra"
 shows "\<exists>S\<in>weyl_algebra.
   (\<forall>d\<in>biv_support (pbw_symbol S). pair_grade d=g) \<and>
   pbw_symbol S=weighted_component 1 (-1) g (pbw_symbol T)"
proof -
 obtain S where S: "S\<in>weyl_algebra"
   and grade: "\<forall>d\<in>biv_support (pbw_symbol S). pair_grade d=g"
   and coeff: "\<forall>i j. pbw_coeff S i j=(if int i-int j=g then pbw_coeff T i j else 0)"
   using exists_exact_grade_projection[OF T, where g=g] by blast
 have symbol: "pbw_symbol S=weighted_component 1 (-1) g (pbw_symbol T)"
 proof (rule biv_eqI)
  fix i j
  show "biv_coeff (pbw_symbol S) i j=biv_coeff (weighted_component 1 (-1) g (pbw_symbol T)) i j"
   using coeff[rule_format, of i j]
   by (simp add: weyl_symbol_coeff[OF S] weyl_symbol_coeff[OF T] weighted_component_coeff pair_weight_def)
 qed
 show ?thesis using S grade symbol by blast
qed

lemma exists_nonzero_exact_grade_projection:
 fixes T :: "complex poly_operator"
 assumes T: "T\<in>weyl_algebra"
   and inhabited: "\<exists>d\<in>biv_support (pbw_symbol T). pair_grade d=g"
 shows "\<exists>S\<in>weyl_algebra. S\<noteq>0 \<and>
   (\<forall>d\<in>biv_support (pbw_symbol S). pair_grade d=g) \<and>
   (\<forall>i j. pbw_coeff S i j=(if int i-int j=g then pbw_coeff T i j else 0))"
proof -
 obtain S where S: "S\<in>weyl_algebra"
   and grade: "\<forall>d\<in>biv_support (pbw_symbol S). pair_grade d=g"
   and coeff: "\<forall>i j. pbw_coeff S i j=(if int i-int j=g then pbw_coeff T i j else 0)"
   using exists_exact_grade_projection[OF T, where g=g] by blast
 obtain d where d: "d\<in>biv_support (pbw_symbol T)" and dg: "pair_grade d=g"
   using inhabited by blast
 have tnz: "pbw_coeff T (fst d) (snd d)\<noteq>0"
   using d by (simp add: weyl_symbol_support[OF T] pbw_pair_support_def)
 have snz: "pbw_coeff S (fst d) (snd d)\<noteq>0"
   using coeff[rule_format, of "fst d" "snd d"] tnz dg
   by (simp add: pair_grade_def)
 have nonzero: "S\<noteq>0" using snz by (auto simp: pbw_coeff_def coeff_poly_def)
 show ?thesis using S nonzero grade coeff by blast
qed
end
