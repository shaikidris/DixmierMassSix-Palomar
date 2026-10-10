theory Polynomial_Finite_Cut_Companion
  imports "Ramified_Two_Bracket_Scalar_Fixed_Point"
    "Ramified_Homogeneous_Polynomial_Realization"
begin

lemma ramified_scalar_fixed_point_realizes_homogeneous_companion:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Pnz: "P\<noteq>0"
    and lattice: "PolynomialWeightLattice rho (int l*sigma) (int l*(rho+sigma)) q"
    and fixed: "[:of_int (ramified_weight_deg l rho sigma P):]*ramified_top_face_polynomial l rho sigma P*pderiv q-
      [:of_int (int l*(rho+sigma)):]*pderiv (ramified_top_face_polynomial l rho sigma P)*q=
      -[:of_nat l*of_int rho:]*ramified_top_face_polynomial l rho sigma P"
  shows "\<exists>F\<in>ramified_operator_algebra l. F\<noteq>0 \<and>
    (\<forall>p\<in>ramified_pbw_support l F. ramified_weight l rho sigma p=int l*(rho+sigma)) \<and>
    ramified_weight_deg l rho sigma F=int l*(rho+sigma) \<and>
    ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P \<and>
    ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
proof -
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?d = "of_nat l*of_int rho::complex"
  let ?b = "int l*(rho+sigma)"
  have f: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
  have dne: "?d\<noteq>0" using l rho by simp
  have constant_nz: "([:?d:]::complex poly)\<noteq>0" using dne by simp
  have q: "q\<noteq>0"
  proof
    assume zero: "q=0"
    have impossible: "(0::complex poly)= -[:?d:]*?f" using fixed by (simp only: zero pderiv_0 mult_zero_right diff_self)
    show False using impossible constant_nz f by simp
  qed
  let ?F = "ramifiedPolynomialFace l rho sigma ?b q"
  have Fc: "?F\<in>ramified_operator_algebra l" by (rule ramifiedPolynomialFace_carrier)
  have Fnz: "?F\<noteq>0" by (rule ramifiedPolynomialFace_ne_zero[OF l q lattice])
  have degree: "ramified_weight_deg l rho sigma ?F=?b" by (rule ramifiedPolynomialFace_weight[OF l q lattice])
  have top: "ramified_top_face_polynomial l rho sigma ?F=q" by (rule ramifiedPolynomialFace_top_face[OF l rho q lattice])
  have cleared: "[:?d:]*ramified_face_centralization l rho sigma P ?F=[:?d:]*(-?f)"
    using ramifiedFaceCentralization_clear_denominator[OF l rho, where P=P and R="?F" and sigma=sigma] fixed
    by (simp only: degree top mult_minus_right minus_mult_left)
  have central: "ramified_face_centralization l rho sigma P ?F= -?f"
    using cleared by (simp only: mult_left_cancel[OF constant_nz])
  have bracket: "ramified_face_bracket l rho sigma P ?F=?f"
    by (simp only: ramified_face_bracket_eq_neg_centralization central minus_minus)
  have bracketnz: "ramified_face_bracket l rho sigma P ?F\<noteq>0" by (subst bracket; rule f)
  have commdegree: "ramified_weight_deg l rho sigma (laurent_comp P ?F-laurent_comp ?F P)=ramified_weight_deg l rho sigma P"
    using ramified_noncentralizing_commutator_weight[OF l rho positive P Fc Pnz Fnz bracketnz] by (simp only: degree add_diff_cancel_right')
  have commface: "ramified_top_face_polynomial l rho sigma (laurent_comp P ?F-laurent_comp ?F P)=?f"
    by (simp only: ramified_noncentralizing_commutator_top_face[OF l rho positive P Fc Pnz Fnz bracketnz] bracket)
  have support: "\<forall>p\<in>ramified_pbw_support l ?F. ramified_weight l rho sigma p=?b"
    using ramifiedPolynomialFace_support_weight[OF l lattice] by blast
  show ?thesis by (intro bexI[of _ "?F"] Fc conjI Fnz support degree commdegree commface)
qed

lemma ramified_two_bracket_homogeneous_companion_exists:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and degree: "0<ramified_weight_deg l rho sigma P"
    and witness: "RamifiedJosephTwoBracketAt l rho sigma P R n"
  shows "\<exists>F\<in>ramified_operator_algebra l. F\<noteq>0 \<and>
    (\<forall>p\<in>ramified_pbw_support l F. ramified_weight l rho sigma p=int l*(rho+sigma)) \<and>
    ramified_weight_deg l rho sigma F=int l*(rho+sigma) \<and>
    ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P \<and>
    ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
proof -
  obtain q where lattice: "PolynomialWeightLattice rho (int l*sigma) (int l*(rho+sigma)) q" and fixed:
    "[:of_int (ramified_weight_deg l rho sigma P):]*ramified_top_face_polynomial l rho sigma P*pderiv q-
      [:of_int (int l*(rho+sigma)):]*pderiv (ramified_top_face_polynomial l rho sigma P)*q=
      -[:of_nat l*of_int rho:]*ramified_top_face_polynomial l rho sigma P"
    using ramified_two_bracket_scalar_fixed_point_with_lattice[OF l rho positive P R Pnz degree witness] by blast
  show ?thesis by (rule ramified_scalar_fixed_point_realizes_homogeneous_companion[OF l rho positive P Pnz lattice fixed])
qed

lemma finite_cut_generated_homogeneous_companion_exists:
  assumes l: "0<l" and history: "admissible_ramified_history l cuts"
    and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and rho: "0<rho" and positive: "0<rho+sigma"
    and Unz: "finite_cut_image l cuts P\<noteq>0"
    and degree: "0<ramified_weight_deg l rho sigma (finite_cut_image l cuts P)"
  shows "\<exists>G\<in>ramified_operator_algebra l. G\<noteq>0 \<and>
    (\<forall>p\<in>ramified_pbw_support l G. ramified_weight l rho sigma p=int l*(rho+sigma)) \<and>
    ramified_weight_deg l rho sigma G=int l*(rho+sigma) \<and>
    ramified_weight_deg l rho sigma
      (laurent_comp (finite_cut_image l cuts P) G-laurent_comp G (finite_cut_image l cuts P))=
      ramified_weight_deg l rho sigma (finite_cut_image l cuts P) \<and>
    ramified_top_face_polynomial l rho sigma
      (laurent_comp (finite_cut_image l cuts P) G-laurent_comp G (finite_cut_image l cuts P))=
      ramified_top_face_polynomial l rho sigma (finite_cut_image l cuts P)"
proof -
  have degree_ne: "ramified_weight_deg l rho sigma (finite_cut_image l cuts P)\<noteq>0" using degree by simp
  obtain R n where R: "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}"
    and witness: "RamifiedJosephTwoBracketAt l rho sigma (finite_cut_image l cuts P) (finite_cut_image l cuts R) n"
    using finite_cut_generated_two_bracket_exists[OF l P Q exact history rho positive Unz degree_ne] by blast
  show ?thesis by (rule ramified_two_bracket_homogeneous_companion_exists[OF l rho positive
    finite_cut_image_carrier[OF l] finite_cut_image_carrier[OF l] Unz degree witness])
qed

end
