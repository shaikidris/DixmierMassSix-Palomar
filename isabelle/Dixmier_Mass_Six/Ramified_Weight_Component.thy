theory Ramified_Weight_Component
  imports "Finite_Cut_Linear_Transport"
    "Ramified_Face_Centralizer_Line"
begin

text \<open>Fixed weight components retain actual PBW coefficients at the unique
Laurent index of each derivative order. They do not require rho to divide l.\<close>

definition ramified_weight_component_polynomial ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> laurent_operator \<Rightarrow> complex poly" where
  "ramified_weight_component_polynomial l rho sigma b T=
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      monom (if rho dvd b-int l*sigma*int j
        then ramified_pbw_coeff l T ((b-int l*sigma*int j) div rho) j else 0) j)"

lemma ramified_weight_component_coeff:
  "coeff (ramified_weight_component_polynomial l rho sigma b T) j=
    (if rho dvd b-int l*sigma*int j
      then ramified_pbw_coeff l T ((b-int l*sigma*int j) div rho) j else 0)"
  by (cases "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)")
    (simp_all add: ramified_weight_component_polynomial_def coeff_sum ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)

lemma ramified_weight_component_add:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and U: "U\<in>ramified_operator_algebra l"
  shows "ramified_weight_component_polynomial l rho sigma b (T+U)=
    ramified_weight_component_polynomial l rho sigma b T+ramified_weight_component_polynomial l rho sigma b U"
  by (rule poly_eqI) (simp add: ramified_weight_component_coeff ramified_pbw_coeff_def
    ramified_pbw_coeffs_add[OF l T U] Poly_Mapping.lookup_add split: if_splits)

lemma ramified_weight_component_smult:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
  shows "ramified_weight_component_polynomial l rho sigma b (normal_smult c T)=
    smult c (ramified_weight_component_polynomial l rho sigma b T)"
  by (rule poly_eqI) (simp add: ramified_weight_component_coeff ramified_pbw_coeff_def
    ramified_pbw_coeffs_smult[OF l T] split: if_splits)

lemma ramified_weight_component_coeff_on_grade:
  assumes rho: "rho\<noteq>0" and grade: "ramified_weight l rho sigma (i,j)=b"
  shows "coeff (ramified_weight_component_polynomial l rho sigma b T) j=ramified_pbw_coeff l T i j"
proof -
  have numerator: "b-int l*sigma*int j=rho*i"
    using grade by (simp add: ramified_weight_def)
  show ?thesis by (simp only: ramified_weight_component_coeff numerator) (simp add: rho)
qed

lemma ramified_weight_component_zero_iff:
  assumes rho: "rho\<noteq>0"
  shows "ramified_weight_component_polynomial l rho sigma b T=0 \<longleftrightarrow>
    (\<forall>i j. ramified_weight l rho sigma (i,j)=b \<longrightarrow> ramified_pbw_coeff l T i j=0)"
proof
  assume zero: "ramified_weight_component_polynomial l rho sigma b T=0"
  show "\<forall>i j. ramified_weight l rho sigma (i,j)=b \<longrightarrow> ramified_pbw_coeff l T i j=0"
  proof (intro allI impI)
    fix i j assume grade: "ramified_weight l rho sigma (i,j)=b"
    have coefficient: "coeff (ramified_weight_component_polynomial l rho sigma b T) j=ramified_pbw_coeff l T i j"
      by (rule ramified_weight_component_coeff_on_grade[OF rho grade])
    show "ramified_pbw_coeff l T i j=0" using coefficient by (simp only: zero coeff_0)
  qed
next
  assume all: "\<forall>i j. ramified_weight l rho sigma (i,j)=b \<longrightarrow> ramified_pbw_coeff l T i j=0"
  show "ramified_weight_component_polynomial l rho sigma b T=0"
  proof (rule poly_eqI)
    fix j
    show "coeff (ramified_weight_component_polynomial l rho sigma b T) j=coeff (0::complex poly) j"
    proof (cases "rho dvd b-int l*sigma*int j")
      case False then show ?thesis by (simp only: ramified_weight_component_coeff False if_False coeff_0)
    next
      case True
      let ?i = "(b-int l*sigma*int j) div rho"
      have grade: "ramified_weight l rho sigma (?i,j)=b"
        by (simp add: ramified_weight_def dvd_mult_div_cancel[OF True])
      have zero: "ramified_pbw_coeff l T ?i j=0" using all grade by blast
      show ?thesis by (simp only: ramified_weight_component_coeff True if_True zero coeff_0)
    qed
  qed
qed

lemma ramified_weight_component_at_degree:
  assumes l: "0<l" and rho: "0<rho" and T: "T\<in>ramified_operator_algebra l"
  shows "ramified_weight_component_polynomial l rho sigma (ramified_weight_deg l rho sigma T) T=
    ramified_top_face_polynomial l rho sigma T"
proof (rule poly_eqI)
  fix j
  have rho_ne: "rho\<noteq>0" using rho by arith
  let ?b = "ramified_weight_deg l rho sigma T"
  let ?t = "ramified_pbw_top_laurent l T j"
  let ?num = "?b-int l*sigma*int j"
  show "coeff (ramified_weight_component_polynomial l rho sigma ?b T) j=
    coeff (ramified_top_face_polynomial l rho sigma T) j"
  proof (cases "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)")
    case False
    then show ?thesis by (simp add: ramified_weight_component_coeff
      ramified_top_face_polynomial_coeff ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
  next
    case True
    note outer_key = True
    have topnz: "ramified_pbw_coeff l T ?t j\<noteq>0"
      using ramified_pbw_top_laurent_mem[OF True]
      by (simp only: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff; simp)
    have topsupport: "(?t,j)\<in>ramified_pbw_support l T"
      using ramified_pbw_support_mem_iff[OF l T] topnz by blast
    have upper: "rho*?t+int l*sigma*int j\<le>?b"
      using ramified_weight_deg_upper[OF topsupport, where rho=rho and sigma=sigma]
      by (simp only: ramified_weight_def fst_conv snd_conv)
    show ?thesis
    proof (cases "rho*?t+int l*sigma*int j=?b")
      case True
      note top_equal = True
      have num: "?num=rho*?t" using top_equal by arith
      show ?thesis by (simp add: ramified_weight_component_coeff ramified_top_face_polynomial_coeff
        outer_key top_equal num rho_ne)
    next
      case False
      note top_unequal = False
      have strict: "rho*?t+int l*sigma*int j<?b" using upper top_unequal by arith
      have componentzero: "coeff (ramified_weight_component_polynomial l rho sigma ?b T) j=0"
      proof (cases "rho dvd ?num")
        case False
        then show ?thesis by (simp only: ramified_weight_component_coeff False if_False)
      next
        case True
        note divides = True
        have reconstruct: "rho*(?num div rho)=?num"
          by (rule dvd_mult_div_cancel[OF divides])
        have products: "rho*?t<rho*(?num div rho)" using strict reconstruct by arith
        have above: "?t<?num div rho" using products by (simp only: mult_less_cancel_left_pos[OF rho])
        have zero: "ramified_pbw_coeff l T (?num div rho) j=0"
          using laurent_upper_coeff_zero_above[OF ramified_pbw_top_laurent_upper above]
          by (simp only: ramified_pbw_coeff_def)
        show ?thesis by (simp only: ramified_weight_component_coeff divides if_True zero)
      qed
      show ?thesis by (simp only: componentzero ramified_top_face_polynomial_coeff outer_key if_True top_unequal if_False)
    qed
  qed
qed

end
