theory Ramified_Laurent_Core
  imports "HOL-Library.Poly_Mapping" "HOL-Computational_Algebra.Polynomial"
begin

text \<open>Finite integer-exponent Laurent polynomials over the actual complex
field. Multiplication is the native additive-exponent convolution. The parameter
l is natural and may be zero: complex division is total, as in the Lean source.\<close>

type_synonym ramified_laurent = "(int, complex) poly_mapping"
type_synonym laurent_operator = "ramified_laurent \<Rightarrow> ramified_laurent"

definition laurent_T :: "int \<Rightarrow> ramified_laurent" where
  "laurent_T n = Poly_Mapping.single n 1"

definition laurent_smult :: "complex \<Rightarrow> ramified_laurent \<Rightarrow> ramified_laurent" where
  "laurent_smult c f = Poly_Mapping.map ((*) c) f"

definition laurent_linear :: "laurent_operator \<Rightarrow> bool" where
  "laurent_linear F \<longleftrightarrow>
    (\<forall>f g. F (f + g) = F f + F g) \<and>
    (\<forall>c f. F (laurent_smult c f) = laurent_smult c (F f))"

definition ramified_derivative :: "nat \<Rightarrow> laurent_operator" where
  "ramified_derivative l f =
    (\<Sum>n\<in>Poly_Mapping.keys f.
      Poly_Mapping.single (n - int l)
        (((of_int n :: complex) / of_nat l) * Poly_Mapping.lookup f n))"

lemma laurent_smult_lookup [simp]:
  "Poly_Mapping.lookup (laurent_smult c f) n = c * Poly_Mapping.lookup f n"
  by (simp add: laurent_smult_def Poly_Mapping.map.rep_eq when_def)

lemma laurent_smult_single:
  "laurent_smult c (Poly_Mapping.single n a) = Poly_Mapping.single n (c * a)"
  by (simp add: laurent_smult_def)

lemma laurent_smult_as_multiplication:
  "laurent_smult c f = Poly_Mapping.single 0 c * f"
  by (simp add: laurent_smult_def Poly_Mapping.mult_map_scale_conv_mult)

lemma laurent_T_mult:
  "laurent_T m * laurent_T n = laurent_T (m + n)"
  by (simp add: laurent_T_def Poly_Mapping.mult_single)

lemma ramified_derivative_lookup:
  "Poly_Mapping.lookup (ramified_derivative l f) k =
    ((of_int (k + int l) :: complex) / of_nat l) *
      Poly_Mapping.lookup f (k + int l)"
proof -
  have shift: "n - int l = k \<longleftrightarrow> n = k + int l" for n :: int
    by arith
  show ?thesis
    by (auto simp: ramified_derivative_def Poly_Mapping.lookup_sum
      Poly_Mapping.lookup_single when_def shift Poly_Mapping.in_keys_iff)
qed

lemma ramified_derivative_support:
  "Poly_Mapping.keys (ramified_derivative l f) \<subseteq>
    (\<lambda>n. n - int l) ` Poly_Mapping.keys f"
proof
  fix k assume "k \<in> Poly_Mapping.keys (ramified_derivative l f)"
  then have "k + int l \<in> Poly_Mapping.keys f"
    by (auto simp: Poly_Mapping.in_keys_iff ramified_derivative_lookup)
  then show "k \<in> (\<lambda>n. n - int l) ` Poly_Mapping.keys f"
    by (force intro!: image_eqI[where x="k + int l"])
qed

lemma ramified_derivative_shift_finite:
  "finite ((\<lambda>n. n - int l) ` Poly_Mapping.keys f)"
  by simp

lemma ramified_derivative_zero [simp]: "ramified_derivative l 0 = 0"
  by (simp add: ramified_derivative_def)

lemma ramified_derivative_add:
  "ramified_derivative l (f + g) = ramified_derivative l f + ramified_derivative l g"
  by (rule poly_mapping_eqI)
     (simp add: ramified_derivative_lookup Poly_Mapping.lookup_add algebra_simps)

lemma ramified_derivative_smult:
  "ramified_derivative l (laurent_smult c f) =
    laurent_smult c (ramified_derivative l f)"
  by (rule poly_mapping_eqI)
     (simp add: ramified_derivative_lookup algebra_simps)

lemma ramified_derivative_linear:
  "laurent_linear (ramified_derivative l)"
  by (simp add: laurent_linear_def ramified_derivative_add ramified_derivative_smult)

lemma ramified_derivative_single:
  "ramified_derivative l (Poly_Mapping.single n c) =
    laurent_smult (((of_int n :: complex) / of_nat l) * c)
      (laurent_T (n - int l))"
  by (cases "c = 0")
     (simp_all add: ramified_derivative_def laurent_T_def laurent_smult_single)

lemma ramified_derivative_T:
  "ramified_derivative l (laurent_T n) =
    laurent_smult ((of_int n :: complex) / of_nat l) (laurent_T (n - int l))"
  using ramified_derivative_single[of l n 1]
  by (simp add: laurent_T_def)

lemma ramified_derivative_zero_parameter:
  "ramified_derivative 0 f = 0"
  by (rule poly_mapping_eqI) (simp add: ramified_derivative_lookup)

end
