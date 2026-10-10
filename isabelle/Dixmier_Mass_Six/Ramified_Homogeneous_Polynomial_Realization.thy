theory Ramified_Homogeneous_Polynomial_Realization
  imports "Ramified_Weight_Component"
    "Polynomial_Quotient_Weight_Lattice"
begin

definition ramifiedPolynomialFaceData :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex poly \<Rightarrow> ramified_pbw_coefficients" where
  "ramifiedPolynomialFaceData l rho sigma b f=
    (\<Sum>j\<in>polynomial_support f. Poly_Mapping.single j
      (Poly_Mapping.single ((b-int l*sigma*int j) div rho) (coeff f j)))"

definition ramifiedPolynomialFace where
  "ramifiedPolynomialFace l rho sigma b f=ramified_normal_eval l (ramifiedPolynomialFaceData l rho sigma b f)"

lemma ramifiedPolynomialFaceData_lookup:
  "Poly_Mapping.lookup (ramifiedPolynomialFaceData l rho sigma b f) j=
    Poly_Mapping.single ((b-int l*sigma*int j) div rho) (coeff f j)"
proof -
  have collapse: "Poly_Mapping.lookup (ramifiedPolynomialFaceData l rho sigma b f) j=
    (if j\<in>polynomial_support f then
      Poly_Mapping.single ((b-int l*sigma*int j) div rho) (coeff f j) else 0)"
    by (simp only: ramifiedPolynomialFaceData_def Poly_Mapping.lookup_sum
      Poly_Mapping.lookup_single when_def sum.delta[OF polynomial_support_finite])
  show ?thesis by (simp only: collapse) (simp add: polynomial_support_def)
qed

lemma ramifiedPolynomialFace_carrier:
  "ramifiedPolynomialFace l rho sigma b f\<in>ramified_operator_algebra l"
unfolding ramifiedPolynomialFace_def ramified_normal_eval_def
proof (rule ramified_algebra_sum[OF Poly_Mapping.finite_keys])
  fix j
  assume "j\<in>Poly_Mapping.keys (ramifiedPolynomialFaceData l rho sigma b f)"
  show "laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup (ramifiedPolynomialFaceData l rho sigma b f) j))
    (ramified_derivative l ^^ j)\<in>ramified_operator_algebra l"
    using normal_atom_mem normal_span_le_operator by blast
qed

lemma ramifiedPolynomialFace_coeff:
  assumes l: "0<l"
  shows "ramified_pbw_coeff l (ramifiedPolynomialFace l rho sigma b f) i j=
    (if (b-int l*sigma*int j) div rho=i then coeff f j else 0)"
proof -
  have data: "ramified_pbw_coeffs l (ramifiedPolynomialFace l rho sigma b f)=ramifiedPolynomialFaceData l rho sigma b f"
    by (rule ramified_pbw_coeffs_eq_of_eval[OF l ramifiedPolynomialFace_carrier])
      (simp only: ramifiedPolynomialFace_def)
  show ?thesis by (simp add: ramified_pbw_coeff_def data ramifiedPolynomialFaceData_lookup
    Poly_Mapping.lookup_single when_def)
qed

lemma ramifiedPolynomialFace_support_iff:
  assumes l: "0<l"
  shows "(i,j)\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f) \<longleftrightarrow>
    coeff f j\<noteq>0 \<and> i=(b-int l*sigma*int j) div rho"
  by (simp only: ramified_pbw_support_mem_iff[OF l ramifiedPolynomialFace_carrier]
    ramifiedPolynomialFace_coeff[OF l]) auto

lemma ramifiedPolynomialFace_support_weight:
  assumes l: "0<l" and lattice: "PolynomialWeightLattice rho (int l*sigma) b f"
    and support: "p\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f)"
  shows "ramified_weight l rho sigma p=b"
proof -
  obtain i j where p: "p=(i,j)" by (cases p) auto
  have supported: "(i,j)\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f)"
    using support by (simp only: p)
  have data: "coeff f j\<noteq>0 \<and> i=(b-int l*sigma*int j) div rho"
    by (rule iffD1[OF ramifiedPolynomialFace_support_iff[OF l] supported])
  have coefficient: "coeff f j\<noteq>0" by (rule conjunct1[OF data])
  have index: "i=(b-int l*sigma*int j) div rho" by (rule conjunct2[OF data])
  have divides: "rho dvd b-int l*sigma*int j"
    using lattice coefficient by (simp add: PolynomialWeightLattice_def)
  have cancel: "rho*((b-int l*sigma*int j) div rho)=b-int l*sigma*int j"
    by (rule dvd_mult_div_cancel[OF divides])
  show ?thesis using cancel by (simp only: p ramified_weight_def fst_conv snd_conv index; arith)
qed

lemma ramifiedPolynomialFace_component:
  assumes l: "0<l" and lattice: "PolynomialWeightLattice rho (int l*sigma) b f"
  shows "ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)=f"
proof (rule poly_eqI)
  fix j
  have occupied: "coeff f j\<noteq>0 \<Longrightarrow> rho dvd b-int l*sigma*int j"
    using lattice by (simp add: PolynomialWeightLattice_def)
  show "coeff (ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)) j=coeff f j"
    using occupied by (simp only: ramified_weight_component_coeff ramifiedPolynomialFace_coeff[OF l] if_True)
      (auto split: if_splits)
qed

lemma ramifiedPolynomialFace_ne_zero:
  assumes l: "0<l" and f: "f\<noteq>0" and lattice: "PolynomialWeightLattice rho (int l*sigma) b f"
  shows "ramifiedPolynomialFace l rho sigma b f\<noteq>0"
proof
  assume zero: "ramifiedPolynomialFace l rho sigma b f=0"
  have componentzero: "ramified_weight_component_polynomial l rho sigma b (0::laurent_operator)=0"
    by (rule poly_eqI) (simp add: ramified_weight_component_coeff ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l])
  have identity: "ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)=f"
    by (rule ramifiedPolynomialFace_component[OF l lattice])
  have "f=0"
  proof -
    have "f=ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)"
      by (rule identity[symmetric])
    also have "...=ramified_weight_component_polynomial l rho sigma b (0::laurent_operator)"
      by (simp only: zero)
    also have "...=0" by (rule componentzero)
    finally show ?thesis .
  qed
  then show False using f by contradiction
qed

lemma ramifiedPolynomialFace_weight:
  assumes l: "0<l" and f: "f\<noteq>0" and lattice: "PolynomialWeightLattice rho (int l*sigma) b f"
  shows "ramified_weight_deg l rho sigma (ramifiedPolynomialFace l rho sigma b f)=b"
proof -
  have nonzero: "ramifiedPolynomialFace l rho sigma b f\<noteq>0"
    by (rule ramifiedPolynomialFace_ne_zero[OF l f lattice])
  have nonempty: "ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f)\<noteq>{}"
    by (rule ramified_pbw_support_nonempty_of_ne_zero[OF l ramifiedPolynomialFace_carrier nonzero])
  obtain p where p: "p\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f)" using nonempty by blast
  show ?thesis
  proof (rule ramified_weight_deg_eq_of_attained_upper)
    show "\<exists>p\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f). ramified_weight l rho sigma p=b"
      by (intro bexI[of _ p] p ramifiedPolynomialFace_support_weight[OF l lattice p])
    show "\<forall>p\<in>ramified_pbw_support l (ramifiedPolynomialFace l rho sigma b f). ramified_weight l rho sigma p\<le>b"
      using ramifiedPolynomialFace_support_weight[OF l lattice] by blast
  qed
qed

lemma ramifiedPolynomialFace_top_face:
  assumes l: "0<l" and rho: "0<rho" and f: "f\<noteq>0" and lattice: "PolynomialWeightLattice rho (int l*sigma) b f"
  shows "ramified_top_face_polynomial l rho sigma (ramifiedPolynomialFace l rho sigma b f)=f"
proof -
  have identity: "ramified_weight_component_polynomial l rho sigma
    (ramified_weight_deg l rho sigma (ramifiedPolynomialFace l rho sigma b f))
    (ramifiedPolynomialFace l rho sigma b f)=ramified_top_face_polynomial l rho sigma (ramifiedPolynomialFace l rho sigma b f)"
    by (rule ramified_weight_component_at_degree[OF l rho ramifiedPolynomialFace_carrier])
  have degree: "ramified_weight_deg l rho sigma (ramifiedPolynomialFace l rho sigma b f)=b"
    by (rule ramifiedPolynomialFace_weight[OF l f lattice])
  have component: "ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)=f"
    by (rule ramifiedPolynomialFace_component[OF l lattice])
  have "ramified_top_face_polynomial l rho sigma (ramifiedPolynomialFace l rho sigma b f)=
    ramified_weight_component_polynomial l rho sigma (ramified_weight_deg l rho sigma (ramifiedPolynomialFace l rho sigma b f))
      (ramifiedPolynomialFace l rho sigma b f)" by (rule identity[symmetric])
  also have "...=ramified_weight_component_polynomial l rho sigma b (ramifiedPolynomialFace l rho sigma b f)"
    by (simp only: degree)
  also have "...=f" by (rule component)
  finally show ?thesis .
qed

end
