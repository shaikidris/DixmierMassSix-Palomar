theory Polynomial_Ramified_Lift_Homomorphism
  imports Polynomial_Ramified_Lift_Data
begin

lemma ramifiedOperator_eq_of_pbwCoeff:
  assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and coefficients: "\<And>i j. ramified_pbw_coeff l P i j=ramified_pbw_coeff l Q i j"
  shows "P=Q"
proof -
  have data: "ramified_pbw_coeffs l P=ramified_pbw_coeffs l Q"
  proof (rule poly_mapping_eqI)
    fix j
    show "Poly_Mapping.lookup (ramified_pbw_coeffs l P) j=Poly_Mapping.lookup (ramified_pbw_coeffs l Q) j"
    proof (rule poly_mapping_eqI)
      fix i
      show "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) i=
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) j) i"
        using coefficients[of i j] by (simp only: ramified_pbw_coeff_def)
    qed
  qed
  show ?thesis using data ramified_pbw_coeffs_eval[OF l P] ramified_pbw_coeffs_eval[OF l Q] by metis
qed

lemma lift_ramified_coefficient_add:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and U: "U\<in>ramified_operator_algebra l"
  shows "ramified_pbw_coeff l (T+U) i j=ramified_pbw_coeff l T i j+ramified_pbw_coeff l U i j"
  by (simp add: ramified_pbw_coeff_def ramified_pbw_coeffs_add[OF l T U] Poly_Mapping.lookup_add)

lemma lift_ramified_coefficient_smult:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
  shows "ramified_pbw_coeff l (normal_smult c T) i j=c*ramified_pbw_coeff l T i j"
  by (simp add: ramified_pbw_coeff_def ramified_pbw_coeffs_smult[OF l T]
    ramified_pbw_smult_lookup laurent_smult_lookup)

lemma polynomial_ramified_lift_add:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
  shows "polynomial_ramified_lift l (P+Q)=polynomial_ramified_lift l P+polynomial_ramified_lift l Q"
proof -
  have PQ: "P+Q\<in>weyl_algebra" using P Q by (auto simp: weyl_algebra_def intro: op_adjoin.add)
  have image: "polynomial_ramified_lift l P+polynomial_ramified_lift l Q\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_add[OF polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
  show ?thesis
  proof (rule ramifiedOperator_eq_of_pbwCoeff[OF l polynomial_ramified_lift_carrier image])
    fix i j
    show "ramified_pbw_coeff l (polynomial_ramified_lift l (P+Q)) i j=
      ramified_pbw_coeff l (polynomial_ramified_lift l P+polynomial_ramified_lift l Q) i j"
    proof (cases "\<exists>a::nat. i=int l*int a")
      case True
      then obtain a where i: "i=int l*int a" by blast
      show ?thesis by (simp only: i lift_ramified_coefficient_add[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier]
        polynomial_ramified_lift_pbwCoeff_scaled[OF l PQ] polynomial_ramified_lift_pbwCoeff_scaled[OF l P]
        polynomial_ramified_lift_pbwCoeff_scaled[OF l Q] pbw_coeff_add)
    next
      case False
      have off: "\<And>a::nat. i\<noteq>int l*int a" using False by blast
      show ?thesis by (simp only: lift_ramified_coefficient_add[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier]
        polynomial_ramified_lift_pbwCoeff_zero_off_scaled[OF l off] add_0)
    qed
  qed
qed

lemma polynomial_ramified_lift_smult:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "polynomial_ramified_lift l (\<lambda>p. smult c (P p))=normal_smult c (polynomial_ramified_lift l P)"
proof -
  have scaled: "(\<lambda>p. smult c (P p))\<in>weyl_algebra"
    using P by (auto simp: weyl_algebra_def intro: op_adjoin_smult)
  have image: "normal_smult c (polynomial_ramified_lift l P)\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_smult[OF polynomial_ramified_lift_carrier])
  show ?thesis
  proof (rule ramifiedOperator_eq_of_pbwCoeff[OF l polynomial_ramified_lift_carrier image])
    fix i j
    show "ramified_pbw_coeff l (polynomial_ramified_lift l (\<lambda>p. smult c (P p))) i j=
      ramified_pbw_coeff l (normal_smult c (polynomial_ramified_lift l P)) i j"
    proof (cases "\<exists>a::nat. i=int l*int a")
      case True
      then obtain a where i: "i=int l*int a" by blast
      show ?thesis by (simp only: i lift_ramified_coefficient_smult[OF l polynomial_ramified_lift_carrier]
        polynomial_ramified_lift_pbwCoeff_scaled[OF l scaled] polynomial_ramified_lift_pbwCoeff_scaled[OF l P]
        pbw_coeff_smult)
    next
      case False
      have off: "\<And>a::nat. i\<noteq>int l*int a" using False by blast
      show ?thesis by (simp only: lift_ramified_coefficient_smult[OF l polynomial_ramified_lift_carrier]
        polynomial_ramified_lift_pbwCoeff_zero_off_scaled[OF l off] mult_zero_right)
    qed
  qed
qed

lemma polynomial_ramified_lift_atom:
  "polynomial_ramified_lift l (normal_monomial a b)=
    laurent_comp (ramified_coeff_mul (laurent_T (int l*int a))) (ramified_derivative l ^^ b)"
proof -
  have support: "biv_support (biv_monom (1::complex) a b)={(a,b)}"
    by (auto simp: biv_support_def prod_eq_iff)
  show ?thesis by (simp add: polynomial_ramified_lift_finite_sum pbw_symbol_normal_monomial support laurent_T_def)
qed

lemma polynomial_ramified_lift_id:
  "polynomial_ramified_lift l id=id"
  using polynomial_ramified_lift_atom[where a=0 and b=0 and l=l]
  by (simp add: laurent_T_def ramified_coeff_mul_one)

lemma polynomial_ramified_lift_x:
  "polynomial_ramified_lift l (x_op::complex poly_operator)=ramified_coeff_gen l (laurent_T (int l))"
proof -
  have atom: "normal_monomial 1 0=(x_op::complex poly_operator)"
    by (simp add: normal_monomial_def funpow_Suc_right)
  show ?thesis using polynomial_ramified_lift_atom[where a=1 and b=0 and l=l]
    by (simp only: atom of_nat_1 mult_1_right funpow.simps(1) laurent_comp_id ramified_coeff_gen_def)
qed

lemma polynomial_ramified_lift_y:
  "polynomial_ramified_lift l (y_op::complex poly_operator)=ramified_Y_gen l"
proof -
  have atom: "normal_monomial 0 1=(y_op::complex poly_operator)"
    by (simp add: normal_monomial_def funpow_Suc_right)
  have expanded: "polynomial_ramified_lift l (y_op::complex poly_operator)=
    laurent_comp (ramified_coeff_mul (laurent_T 0)) (ramified_derivative l ^^ 1)"
    using polynomial_ramified_lift_atom[where a=0 and b=1 and l=l]
    by (simp only: atom of_nat_0 mult_zero_right)
  show ?thesis using expanded by (simp add: laurent_T_def ramified_coeff_mul_one
    ramified_Y_gen_def laurent_comp_id)
qed

lemma polynomial_ramified_lift_scalar:
  assumes l: "0<l"
  shows "polynomial_ramified_lift l (op_scalar c)=normal_smult c id"
proof -
  have carrier: "(id::complex poly_operator)\<in>weyl_algebra" by (simp add: weyl_algebra_def)
  show ?thesis using polynomial_ramified_lift_smult[OF l carrier, where c=c]
    by (simp add: op_scalar_def polynomial_ramified_lift_id)
qed

lemma polynomial_ramified_lift_diff:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
  shows "polynomial_ramified_lift l (P-Q)=polynomial_ramified_lift l P-polynomial_ramified_lift l Q"
proof -
  have negative: "(\<lambda>p. smult (-1) (Q p))=-Q" by (rule ext) simp
  have Qnegative: "(-Q)\<in>weyl_algebra"
    using op_adjoin_smult[OF Q[unfolded weyl_algebra_def], where c="-1"]
    by (simp only: negative weyl_algebra_def)
  have mapped_negative: "polynomial_ramified_lift l (-Q)=-polynomial_ramified_lift l Q"
    using polynomial_ramified_lift_smult[OF l Q, where c="-1"]
    by (simp only: negative normal_smult_minus_one)
  show ?thesis using polynomial_ramified_lift_add[OF l P Qnegative]
    by (simp only: mapped_negative diff_conv_add_uminus)
qed

lemma polynomial_ramified_lift_zero [simp]:
  "polynomial_ramified_lift l 0=0"
  by (simp add: polynomial_ramified_lift_def polynomial_ramified_pbw_data_def biv_support_def)

lemma polynomial_ramified_lift_sum:
  assumes l: "0<l" and finite: "finite S"
    and carrier: "\<And>u. u\<in>S \<Longrightarrow> F u\<in>(weyl_algebra::complex poly_operator set)"
  shows "polynomial_ramified_lift l (\<Sum>u\<in>S. F u)=(\<Sum>u\<in>S. polynomial_ramified_lift l (F u))"
  using finite carrier
proof (induction S rule: finite_induct)
  case empty
  show ?case by (simp only: sum.empty polynomial_ramified_lift_zero)
next
  case (insert u S)
  have u: "F u\<in>weyl_algebra" using insert.prems by simp
  have all: "\<And>v. v\<in>S \<Longrightarrow> F v\<in>weyl_algebra" using insert.prems by simp
  have sum: "(\<Sum>v\<in>S. F v)\<in>weyl_algebra"
    using all by (auto simp: weyl_algebra_def intro: op_adjoin_sum)
  have ih: "polynomial_ramified_lift l (\<Sum>v\<in>S. F v)=(\<Sum>v\<in>S. polynomial_ramified_lift l (F v))"
    by (rule insert.IH[OF all])
  show ?case by (simp only: sum.insert[OF insert.hyps] polynomial_ramified_lift_add[OF l u sum] ih)
qed

lemma lift_laurent_T_scaled_power:
  "laurent_T (int l*int a)=laurent_T (int l)^a"
proof (induction a)
  case 0
  show ?case by (simp add: laurent_T_def)
next
  case (Suc a)
  have "laurent_T (int l*int(Suc a))=laurent_T (int l)*laurent_T (int l*int a)"
    by (simp only: laurent_T_mult) (simp add: algebra_simps)
  also have "\<dots>=laurent_T (int l)*laurent_T (int l)^a" by (simp only: Suc.IH)
  also have "\<dots>=laurent_T (int l)^Suc a" by (simp only: power_Suc)
  finally show ?case .
qed

lemma lift_scaled_T_derivative:
  assumes l: "0<l"
  shows "ramified_derivative l (laurent_T (int l*int a))=
    laurent_smult (of_nat a) (laurent_T (int l*int(a-1)))"
  using ramified_derivative_X_pow[OF l, where k=a]
  by (simp only: lift_laurent_T_scaled_power)

lemma lift_normal_atom_smult:
  "normal_atom l (laurent_smult c f,n)=normal_smult c (normal_atom l (f,n))"
  by (rule ext) (simp add: normal_atom_def normal_smult_def laurent_comp_def ramified_coeff_mul_def
    laurent_smult_as_multiplication mult.assoc)

lemma lift_atom_as_normal:
  "polynomial_ramified_lift l (normal_monomial a b)=normal_atom l (laurent_T (int l*int a),b)"
  by (simp only: polynomial_ramified_lift_atom normal_atom_def fst_conv snd_conv)

lemma polynomial_ramified_lift_X_mul_atom:
  "polynomial_ramified_lift l (op_comp x_op (normal_monomial a b))=
    laurent_comp (polynomial_ramified_lift l x_op) (polynomial_ramified_lift l (normal_monomial a b))"
  by (simp add: x_normal_monomial polynomial_ramified_lift_atom polynomial_ramified_lift_x
    ramified_coeff_gen_def laurent_comp_assoc[symmetric] Ramified_Normal_Form.ramified_coeff_mul_mul laurent_T_mult algebra_simps)

lemma polynomial_ramified_lift_Y_mul_atom:
  assumes l: "0<l"
  shows "polynomial_ramified_lift l (op_comp y_op (normal_monomial a b))=
    laurent_comp (polynomial_ramified_lift l y_op) (polynomial_ramified_lift l (normal_monomial a b))"
proof -
  have scalar_carrier: "(\<lambda>p. smult (of_nat a) (normal_monomial (a-1) b p))\<in>(weyl_algebra::complex poly_operator set)"
    by (auto simp: weyl_algebra_def intro: op_adjoin_smult normal_monomial_in_weyl[unfolded weyl_algebra_def])
  have lifted: "polynomial_ramified_lift l (op_comp y_op (normal_monomial a b))=
    normal_smult (of_nat a) (polynomial_ramified_lift l (normal_monomial (a-1) b))+
    polynomial_ramified_lift l (normal_monomial a (Suc b))"
    by (simp only: y_normal_monomial polynomial_ramified_lift_add[OF l scalar_carrier normal_monomial_in_weyl]
      polynomial_ramified_lift_smult[OF l normal_monomial_in_weyl])
  have target: "laurent_comp (polynomial_ramified_lift l y_op) (polynomial_ramified_lift l (normal_monomial a b))=
    polynomial_ramified_lift l (normal_monomial a (Suc b))+
    normal_smult (of_nat a) (polynomial_ramified_lift l (normal_monomial (a-1) b))"
    by (simp only: polynomial_ramified_lift_y ramified_Y_gen_def lift_atom_as_normal normal_atom_derivative
      lift_scaled_T_derivative[OF l] lift_normal_atom_smult)
  show ?thesis using lifted target by (simp add: add.commute)
qed

lemma lift_function_sum_apply:
  fixes F :: "'i \<Rightarrow> 'a \<Rightarrow> 'b::comm_monoid_add"
  assumes "finite S"
  shows "(\<Sum>u\<in>S. F u) x=(\<Sum>u\<in>S. F u x)"
  using assms by (induction S rule: finite_induct) (simp_all add: plus_fun_def zero_fun_def)

lemma lift_poly_comp_sum:
  assumes finite: "finite S" and T: "poly_linear T"
  shows "op_comp T (\<Sum>u\<in>S. F u)=(\<Sum>u\<in>S. op_comp T (F u))"
proof (rule ext)
  fix x
  have application: "(\<Sum>u\<in>S. F u) x=(\<Sum>u\<in>S. F u x)"
    by (rule lift_function_sum_apply[OF finite])
  have image: "T (\<Sum>u\<in>S. F u x)=(\<Sum>u\<in>S. T (F u x))"
    by (rule poly_linear_sum[OF T])
  show "op_comp T (\<Sum>u\<in>S. F u) x=(\<Sum>u\<in>S. op_comp T (F u)) x"
    by (simp only: op_comp_def application image lift_function_sum_apply[OF finite])
qed

lemma lift_poly_comp_smult:
  assumes T: "poly_linear T"
  shows "op_comp T (\<lambda>p. smult c (U p))=(\<lambda>p. smult c (op_comp T U p))"
  using T by (auto simp: poly_linear_def op_comp_def fun_eq_iff)

lemma polynomial_ramified_lift_generator_mul:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and generator: "G=x_op \<or> G=y_op"
  shows "polynomial_ramified_lift l (op_comp G P)=
    laurent_comp (polynomial_ramified_lift l G) (polynomial_ramified_lift l P)"
proof -
  obtain S where finite: "finite S" and reconstruction: "P=finite_normal_sum S (\<lambda>u. pbw_coeff P (fst u) (snd u))"
    using weyl_pbw_reconstruction[OF P] by blast
  let ?c = "\<lambda>u. pbw_coeff P (fst u) (snd u)"
  let ?N = "\<lambda>u. normal_monomial (fst u) (snd u)::complex poly_operator"
  let ?F = "\<lambda>u. (\<lambda>p. smult (?c u) (?N u p))"
  have sum_reconstruction: "P=(\<Sum>u\<in>S. ?F u)"
    using reconstruction by (auto simp: finite_normal_sum_def fun_eq_iff lift_function_sum_apply[OF finite])
  have F: "\<And>u. ?F u\<in>weyl_algebra"
    by (auto simp: weyl_algebra_def intro: op_adjoin_smult normal_monomial_in_weyl[unfolded weyl_algebra_def])
  have G: "G\<in>weyl_algebra" and linearG: "poly_linear G" using generator by auto
  have product: "\<And>u. op_comp G (?N u)\<in>weyl_algebra"
    using G normal_monomial_in_weyl by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
  have imageG: "laurent_linear (polynomial_ramified_lift l G)"
    by (rule ramified_operator_algebra_linear[OF polynomial_ramified_lift_carrier])
  have atoms: "\<And>u. polynomial_ramified_lift l (op_comp G (?N u))=
    laurent_comp (polynomial_ramified_lift l G) (polynomial_ramified_lift l (?N u))"
    using generator polynomial_ramified_lift_X_mul_atom polynomial_ramified_lift_Y_mul_atom[OF l] by blast
  have terms: "\<And>u. polynomial_ramified_lift l (op_comp G (?F u))=
    laurent_comp (polynomial_ramified_lift l G) (polynomial_ramified_lift l (?F u))"
    by (simp only: lift_poly_comp_smult[OF linearG] polynomial_ramified_lift_smult[OF l product]
      polynomial_ramified_lift_smult[OF l normal_monomial_in_weyl] atoms laurent_comp_smult_right[OF imageG])
  have products: "\<And>u. op_comp G (?F u)\<in>weyl_algebra"
    using G F by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
  have "polynomial_ramified_lift l (op_comp G P)=
    (\<Sum>u\<in>S. polynomial_ramified_lift l (op_comp G (?F u)))"
  proof -
    have transported: "polynomial_ramified_lift l (op_comp G P)=
      polynomial_ramified_lift l (op_comp G (\<Sum>u\<in>S. ?F u))"
      by (rule arg_cong[OF sum_reconstruction, of "\<lambda>U. polynomial_ramified_lift l (op_comp G U)"])
    show ?thesis using transported by (simp only: lift_poly_comp_sum[OF finite linearG]
      polynomial_ramified_lift_sum[OF l finite products])
  qed
  also have "\<dots>=(\<Sum>u\<in>S. laurent_comp (polynomial_ramified_lift l G) (polynomial_ramified_lift l (?F u)))"
    by (simp only: terms)
  also have "\<dots>=laurent_comp (polynomial_ramified_lift l G)
    (\<Sum>u\<in>S. polynomial_ramified_lift l (?F u))"
    by (simp only: laurent_comp_sum_right[OF finite imageG])
  also have "\<dots>=laurent_comp (polynomial_ramified_lift l G) (polynomial_ramified_lift l P)"
  proof -
    have transported: "polynomial_ramified_lift l P=polynomial_ramified_lift l (\<Sum>u\<in>S. ?F u)"
      by (rule arg_cong[OF sum_reconstruction])
    have image: "polynomial_ramified_lift l P=(\<Sum>u\<in>S. polynomial_ramified_lift l (?F u))"
      using transported by (simp only: polynomial_ramified_lift_sum[OF l finite F])
    show ?thesis by (simp only: image[symmetric])
  qed
  finally show ?thesis .
qed

lemma polynomial_ramified_lift_X_mul:
  assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "polynomial_ramified_lift l (op_comp x_op P)=
    laurent_comp (polynomial_ramified_lift l x_op) (polynomial_ramified_lift l P)"
  by (rule polynomial_ramified_lift_generator_mul[OF assms]) simp

lemma polynomial_ramified_lift_Y_mul:
  assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "polynomial_ramified_lift l (op_comp y_op P)=
    laurent_comp (polynomial_ramified_lift l y_op) (polynomial_ramified_lift l P)"
  by (rule polynomial_ramified_lift_generator_mul[OF assms]) simp

lemma polynomial_ramified_lift_comp:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
  shows "polynomial_ramified_lift l (op_comp P Q)=
    laurent_comp (polynomial_ramified_lift l P) (polynomial_ramified_lift l Q)"
proof -
  have all: "\<forall>V\<in>weyl_algebra. polynomial_ramified_lift l (op_comp P V)=
    laurent_comp (polynomial_ramified_lift l P) (polynomial_ramified_lift l V)"
    using P[unfolded weyl_algebra_def]
  proof (induction rule: op_adjoin.induct)
    case (generator T)
    show ?case by (intro ballI polynomial_ramified_lift_generator_mul[OF l])
      (use generator.hyps in auto)
  next
    case (scalar c)
    show ?case
    proof (intro ballI)
      fix V :: "complex poly_operator" assume V: "V\<in>weyl_algebra"
      show "polynomial_ramified_lift l (op_comp (op_scalar c) V)=
        laurent_comp (polynomial_ramified_lift l (op_scalar c)) (polynomial_ramified_lift l V)"
      proof -
        have source: "op_comp (op_scalar c) V=(\<lambda>p. smult c (V p))"
          by (simp add: op_comp_def op_scalar_def)
        show ?thesis by (simp only: source polynomial_ramified_lift_smult[OF l V]
          polynomial_ramified_lift_scalar[OF l] laurent_comp_smult_left laurent_comp_id)
      qed
    qed
  next
    case (add T U)
    have T: "T\<in>weyl_algebra" and U: "U\<in>weyl_algebra" using add.hyps by (simp_all only: weyl_algebra_def)
    show ?case
    proof (intro ballI)
      fix V :: "complex poly_operator" assume V: "V\<in>weyl_algebra"
      have TV: "op_comp T V\<in>weyl_algebra" and UV: "op_comp U V\<in>weyl_algebra"
        using T U V by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
      show "polynomial_ramified_lift l (op_comp (T+U) V)=
        laurent_comp (polynomial_ramified_lift l (T+U)) (polynomial_ramified_lift l V)"
        using add.IH V by (auto simp only: op_comp_add_left polynomial_ramified_lift_add[OF l TV UV]
          polynomial_ramified_lift_add[OF l T U] laurent_comp_add_left)
    qed
  next
    case (diff T U)
    have T: "T\<in>weyl_algebra" and U: "U\<in>weyl_algebra" using diff.hyps by (simp_all only: weyl_algebra_def)
    show ?case
    proof (intro ballI)
      fix V :: "complex poly_operator" assume V: "V\<in>weyl_algebra"
      have TV: "op_comp T V\<in>weyl_algebra" and UV: "op_comp U V\<in>weyl_algebra"
        using T U V by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
      have distribute: "op_comp (T-U) V=op_comp T V-op_comp U V" by (simp add: op_comp_def fun_eq_iff)
      have target: "laurent_comp (polynomial_ramified_lift l T-polynomial_ramified_lift l U) (polynomial_ramified_lift l V)=
        laurent_comp (polynomial_ramified_lift l T) (polynomial_ramified_lift l V)-
        laurent_comp (polynomial_ramified_lift l U) (polynomial_ramified_lift l V)"
        by (simp add: laurent_comp_def fun_eq_iff)
      show "polynomial_ramified_lift l (op_comp (T-U) V)=
        laurent_comp (polynomial_ramified_lift l (T-U)) (polynomial_ramified_lift l V)"
        using diff.IH V by (auto simp only: distribute polynomial_ramified_lift_diff[OF l TV UV]
          polynomial_ramified_lift_diff[OF l T U] target)
    qed
  next
    case (comp T U)
    have T: "T\<in>weyl_algebra" and U: "U\<in>weyl_algebra" using comp.hyps by (simp_all only: weyl_algebra_def)
    show ?case
    proof (intro ballI)
      fix V :: "complex poly_operator" assume V: "V\<in>weyl_algebra"
      have UV: "op_comp U V\<in>weyl_algebra" using U V by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
      have TU: "polynomial_ramified_lift l (op_comp T U)=
        laurent_comp (polynomial_ramified_lift l T) (polynomial_ramified_lift l U)"
        using comp.IH U by blast
      have TUV: "polynomial_ramified_lift l (op_comp T (op_comp U V))=
        laurent_comp (polynomial_ramified_lift l T) (polynomial_ramified_lift l (op_comp U V))"
        using comp.IH UV by blast
      have UVimage: "polynomial_ramified_lift l (op_comp U V)=
        laurent_comp (polynomial_ramified_lift l U) (polynomial_ramified_lift l V)"
        using comp.IH V by blast
      show "polynomial_ramified_lift l (op_comp (op_comp T U) V)=
        laurent_comp (polynomial_ramified_lift l (op_comp T U)) (polynomial_ramified_lift l V)"
        by (simp only: op_comp_assoc TU TUV UVimage laurent_comp_assoc)
    qed
  qed
  show ?thesis using all Q by blast
qed

lemma polynomial_ramified_lift_commutator:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
  shows "polynomial_ramified_lift l (op_comp Q P-op_comp P Q)=
    laurent_comp (polynomial_ramified_lift l Q) (polynomial_ramified_lift l P)-
    laurent_comp (polynomial_ramified_lift l P) (polynomial_ramified_lift l Q)"
proof -
  have QP: "op_comp Q P\<in>weyl_algebra" and PQ: "op_comp P Q\<in>weyl_algebra"
    using P Q by (auto simp: weyl_algebra_def intro: op_adjoin.comp)
  show ?thesis by (simp only: polynomial_ramified_lift_diff[OF l QP PQ]
    polynomial_ramified_lift_comp[OF l Q P] polynomial_ramified_lift_comp[OF l P Q])
qed

lemma polynomial_ramified_lift_bracket_one:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and bracket: "op_comp Q P-op_comp P Q=id"
  shows "laurent_comp (polynomial_ramified_lift l Q) (polynomial_ramified_lift l P)-
    laurent_comp (polynomial_ramified_lift l P) (polynomial_ramified_lift l Q)=id"
  using polynomial_ramified_lift_commutator[OF l P Q] bracket
  by (simp only: bracket polynomial_ramified_lift_id)

end
