theory Opposite_Grade_Commutator
  imports "Grade_Normal_Forms"
    "Finite_Difference"
begin

text \<open>Native formalization of OppositeGradeCommutator.lean at
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Exact source order is QP-PQ=id.
The source architecture uses arbitrary opposite homogeneous grades,
Euler shifts, falling/rising factorials, and scalar finite differences.\<close>

definition rising_factorial_poly :: "nat \<Rightarrow> 'k::field poly" where
  "rising_factorial_poly k = (\<Prod>i<k. [:of_nat i,1:])"

lemma rising_factorial_poly_succ:
  "rising_factorial_poly (Suc k) = [:of_nat k,1:] * (rising_factorial_poly k :: 'k::field poly)"
  by (simp add: rising_factorial_poly_def mult.commute)

lemma falling_factorial_poly_succ:
  "fallingFactorialPoly (Suc k) = [:-of_nat (Suc k),1:] * (fallingFactorialPoly k :: 'k::field poly)"
  by (simp add: fallingFactorialPoly_def mult.commute)

lemma falling_comp_add_eq_rising:
  "pcompose (fallingFactorialPoly k) [:of_nat k,1:] = (rising_factorial_poly k :: 'k::field poly)"
proof -
  let ?r = "\<lambda>i. k-Suc i"
  have reflected: "?r ` {..<k} = {..<k}"
  proof (rule set_eqI)
    fix i
    show "i \<in> ?r ` {..<k} \<longleftrightarrow> i \<in> {..<k}"
    proof
      assume "i \<in> ?r ` {..<k}"
      then obtain j where "j<k" "i=k-Suc j" by auto
      then show "i \<in> {..<k}" by (simp; arith)
    next
      assume "i \<in> {..<k}"
      then have i_less: "i<k" by simp
      have less: "k-Suc i<k" using i_less by arith
      have inverse: "k-Suc (k-Suc i)=i" using i_less by arith
      show "i \<in> ?r ` {..<k}" by (rule image_eqI[of _ _ "k-Suc i"]) (simp_all add: inverse less)
    qed
  qed
  have injective: "inj_on ?r {..<k}"
    by (rule inj_onI) (simp; arith)
  have factor: "pcompose [:-of_nat (i+1),1:] [:of_nat k,1:] = ([:of_nat (k-Suc i),1:]::'k poly)"
    if "i<k" for i
  proof -
    have le: "Suc i \<le> k" using that by arith
    have cast: "(of_nat (k-Suc i)::'k) = of_nat k-of_nat (Suc i)"
      by (rule of_nat_diff[OF le])
    show ?thesis by (simp add: pcompose_pCons cast)
  qed
  have "pcompose (fallingFactorialPoly k) [:of_nat k,1:] = (\<Prod>i<k. [:of_nat (?r i),1:]::'k poly)"
    unfolding fallingFactorialPoly_def pcompose_prod
    by (rule prod.cong[OF refl]) (rule factor; simp)
  also have "... = (\<Prod>i<k. [:of_nat i,1:]::'k poly)"
    using prod.reindex[OF injective, of "\<lambda>i. [:of_nat i,1:]::'k poly"] reflected
    by (simp add: comp_def)
  finally show ?thesis unfolding rising_factorial_poly_def .
qed

lemma operator_scalar_power_intertwining:
  fixes S u :: "'k::field poly_operator"
  assumes linear: "poly_linear u"
    and relation: "op_comp u S = op_comp (S+op_scalar c) u"
  shows "(u ^^ k) (S v) = S ((u ^^ k) v) + smult (of_nat k*c) ((u ^^ k) v)"
proof -
  have base: "u (S w) = S (u w)+smult c (u w)" for w
    using fun_cong[OF relation, of w] by (simp add: op_comp_def op_scalar_def)
  show ?thesis
    by (induction k)
      (use linear in \<open>auto simp: funpow.simps(2) o_def poly_linear_def base
        smult_add_left smult_smult algebra_simps\<close>)
qed

lemma ypow_yx_shift_map:
  "op_comp (y_op ^^ k) euler_yx =
    op_comp (euler_yx+op_scalar (of_nat k)) (y_op ^^ k :: 'k::field poly_operator)"
proof -
  have relation: "op_comp y_op euler_yx = op_comp (euler_yx+op_scalar 1) y_op"
    by (rule ext) (simp add: euler_yx_def op_comp_def x_op_def y_op_def
      op_scalar_def pderiv_mult pderiv_add pderiv_pCons algebra_simps)
  show ?thesis by (rule ext)
    (simp only: op_comp_def plus_fun_def op_scalar_def;
      use operator_scalar_power_intertwining[OF poly_linear_y relation, of k] in auto)
qed

lemma xpow_yx_shift_map:
  "op_comp (x_op ^^ k) euler_yx =
    op_comp (euler_yx-op_scalar (of_nat k)) (x_op ^^ k :: 'k::field poly_operator)"
proof -
  have relation: "op_comp x_op euler_yx = op_comp (euler_yx+op_scalar (-1)) x_op"
    by (rule ext) (simp add: euler_yx_def op_comp_def x_op_def y_op_def
      op_scalar_def pderiv_mult pderiv_pCons algebra_simps)
  show ?thesis by (rule ext)
    (simp only: op_comp_def minus_apply op_scalar_def;
      use operator_scalar_power_intertwining[OF poly_linear_x relation, of k] in auto)
qed

lemma eval_comp_add_nat:
  "op_poly_eval (euler_yx :: 'k::field poly_operator) (pcompose p [:of_nat k,1:]) =
    op_poly_eval (euler_yx+op_scalar (of_nat k)) p"
proof -
  have affine: "op_poly_eval (euler_yx :: 'k poly_operator) [:of_nat k,1:] = euler_yx+op_scalar (of_nat k)"
    by (rule ext) (simp add: op_poly_eval_pCons[OF euler_yx_linear]
      op_comp_def op_scalar_def poly_linear_zero_image[OF euler_yx_linear] add.commute)
  show ?thesis by (simp only: op_poly_eval_pcompose[OF euler_yx_linear] affine)
qed

lemma eval_comp_sub_nat:
  "op_poly_eval (euler_yx :: 'k::field poly_operator) (pcompose p [:-of_nat k,1:]) =
    op_poly_eval (euler_yx-op_scalar (of_nat k)) p"
proof -
  have affine: "op_poly_eval (euler_yx :: 'k poly_operator) [:-of_nat k,1:] = euler_yx-op_scalar (of_nat k)"
    by (rule ext) (simp add: op_poly_eval_pCons[OF euler_yx_linear]
      op_comp_def op_scalar_def poly_linear_zero_image[OF euler_yx_linear] smult_minus_left)
  show ?thesis by (simp only: op_poly_eval_pcompose[OF euler_yx_linear] affine)
qed

lemma ypow_aeval_yx_shift:
  "op_comp (y_op ^^ k) (op_poly_eval euler_yx p) =
    op_comp (op_poly_eval euler_yx (pcompose p [:of_nat k,1:])) (y_op ^^ k :: 'k::field poly_operator)"
proof -
  have linear: "poly_linear (y_op ^^ k :: 'k poly_operator)" by (rule poly_linear_power) simp
  show ?thesis using polynomial_aeval_intertwining[OF euler_yx_linear linear poly_linear_scalar ypow_yx_shift_map, of p]
    by (simp only: eval_comp_add_nat)
qed

lemma xpow_aeval_yx_shift:
  "op_comp (x_op ^^ k) (op_poly_eval euler_yx p) =
    op_comp (op_poly_eval euler_yx (pcompose p [:-of_nat k,1:])) (x_op ^^ k :: 'k::field poly_operator)"
proof -
  have linear: "poly_linear (x_op ^^ k :: 'k poly_operator)" by (rule poly_linear_power) simp
  have signed: "euler_yx+op_scalar (-of_nat k)=(euler_yx-op_scalar (of_nat k) :: 'k poly_operator)"
    by (rule ext) (simp add: op_scalar_def smult_minus_left)
  have relation: "op_comp (x_op ^^ k) euler_yx = op_comp (euler_yx+op_scalar (-of_nat k)) (x_op ^^ k :: 'k poly_operator)"
    by (simp only: signed xpow_yx_shift_map)
  show ?thesis using polynomial_aeval_intertwining[OF euler_yx_linear linear poly_linear_scalar relation, of p]
    by (simp only: signed eval_comp_sub_nat)
qed

lemma xpow_ypow_eq_falling:
  "op_comp (x_op ^^ k) (y_op ^^ k) = op_poly_eval euler_yx (fallingFactorialPoly k :: 'k::field poly)"
proof -
  have polynomial: "lower_shift_poly k = (fallingFactorialPoly k :: 'k poly)"
    by (induction k) (simp_all add: fallingFactorialPoly_def mult.commute)
  have basis: "op_poly_eval euler_yx (lower_shift_poly k) = (normal_monomial k k :: 'k poly_operator)"
    using lower_shift_basis[of k 0, where 'k='k] by simp
  show ?thesis using basis polynomial by (simp only: normal_monomial_def)
qed

lemma ypow_xpow_eq_rising:
  "op_comp (y_op ^^ k) (x_op ^^ k) = op_poly_eval euler_yx (rising_factorial_poly k :: 'k::field poly)"
proof (induction k)
  case 0
  show ?case by (simp add: rising_factorial_poly_def op_poly_eval_one[OF euler_yx_linear] op_comp_def fun_eq_iff)
next
  case (Suc k)
  have split: "op_comp (y_op ^^ Suc k) (x_op ^^ Suc k) =
    op_comp (op_comp (y_op ^^ k) euler_yx) (x_op ^^ k :: 'k poly_operator)"
    by (rule ext) (simp add: euler_yx_def op_comp_def funpow_Suc_right funpow.simps(2) o_def funpow_swap1)
  have "op_comp (y_op ^^ Suc k) (x_op ^^ Suc k) =
    op_comp (euler_yx+op_scalar (of_nat k)) (op_comp (y_op ^^ k) (x_op ^^ k :: 'k poly_operator))"
    by (simp only: split ypow_yx_shift_map op_comp_assoc)
  also have "... = op_comp (op_poly_eval euler_yx [:of_nat k,1:]) (op_poly_eval euler_yx (rising_factorial_poly k))"
    by (simp only: Suc.IH op_poly_eval_pCons[OF euler_yx_linear] op_poly_eval_const[OF euler_yx_linear];
      simp add: op_comp_def op_scalar_def fun_eq_iff add.commute poly_linear_zero_image[OF euler_yx_linear])
  also have "... = op_poly_eval euler_yx (rising_factorial_poly (Suc k))"
    by (simp only: op_poly_eval_mult[OF euler_yx_linear, symmetric] rising_factorial_poly_succ)
  finally show ?case .
qed

lemma opposite_grade_normal_form_commutator:
  fixes f g :: "'k::field poly"
  shows "op_comp (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) -
    op_comp (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) =
    op_poly_eval euler_yx (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k -
      f*pcompose g [:of_nat k,1:]*rising_factorial_poly k)"
proof -
  have QP: "op_comp (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) =
    op_poly_eval euler_yx (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k)"
  proof -
    have "op_comp (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) =
      op_comp (op_comp (op_poly_eval euler_yx g) (op_comp (x_op ^^ k) (op_poly_eval euler_yx f))) (y_op ^^ k)"
      by (simp only: op_comp_assoc)
    also have "... = op_comp (op_comp (op_poly_eval euler_yx g)
      (op_comp (op_poly_eval euler_yx (pcompose f [:-of_nat k,1:])) (x_op ^^ k))) (y_op ^^ k)"
      by (simp only: xpow_aeval_yx_shift)
    also have "... = op_comp (op_comp (op_poly_eval euler_yx g)
      (op_poly_eval euler_yx (pcompose f [:-of_nat k,1:]))) (op_comp (x_op ^^ k) (y_op ^^ k))"
      by (simp only: op_comp_assoc)
    also have "... = op_poly_eval euler_yx (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k)"
      by (simp only: xpow_ypow_eq_falling op_poly_eval_mult[OF euler_yx_linear])
    finally show ?thesis .
  qed
  have PQ: "op_comp (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) =
    op_poly_eval euler_yx (f*pcompose g [:of_nat k,1:]*rising_factorial_poly k)"
  proof -
    have "op_comp (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) =
      op_comp (op_comp (op_poly_eval euler_yx f) (op_comp (y_op ^^ k) (op_poly_eval euler_yx g))) (x_op ^^ k)"
      by (simp only: op_comp_assoc)
    also have "... = op_comp (op_comp (op_poly_eval euler_yx f)
      (op_comp (op_poly_eval euler_yx (pcompose g [:of_nat k,1:])) (y_op ^^ k))) (x_op ^^ k)"
      by (simp only: ypow_aeval_yx_shift)
    also have "... = op_comp (op_comp (op_poly_eval euler_yx f)
      (op_poly_eval euler_yx (pcompose g [:of_nat k,1:]))) (op_comp (y_op ^^ k) (x_op ^^ k))"
      by (simp only: op_comp_assoc)
    also have "... = op_poly_eval euler_yx (f*pcompose g [:of_nat k,1:]*rising_factorial_poly k)"
      by (simp only: ypow_xpow_eq_rising op_poly_eval_mult[OF euler_yx_linear])
    finally show ?thesis .
  qed
  show ?thesis by (simp only: QP PQ op_poly_eval_diff[OF euler_yx_linear])
qed

lemma falling_product_comp_add:
  "pcompose (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k) [:of_nat k,1:] =
    (f*pcompose g [:of_nat k,1:]*rising_factorial_poly k :: 'k::field poly)"
  by (simp add: pcompose_mult pcompose_assoc[symmetric] falling_comp_add_eq_rising
    pcompose_pCons mult_ac)

lemma opposite_grade_normal_forms_commutator_eq_scalar:
  fixes f g :: "'k::field_char_0 poly"
  assumes exact: "op_comp (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) -
    op_comp (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) = id"
  shows "g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k -
    pcompose (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k) [:of_nat k,1:] = 1"
proof -
  have evaluated: "op_poly_eval euler_yx (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k -
    pcompose (g*pcompose f [:-of_nat k,1:]*fallingFactorialPoly k) [:of_nat k,1:]) = op_poly_eval euler_yx 1"
    using exact opposite_grade_normal_form_commutator[where f=f and g=g and k=k]
    by (simp only: falling_product_comp_add op_poly_eval_one[OF euler_yx_linear])
  show ?thesis by (rule injD[OF aeval_yx_injective evaluated])
qed

lemma opposite_grade_exact_pair_forces_generator_forms:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra" and positive: "0<k"
    and Pgrade: "\<And>u. u \<in> biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u = -int k"
    and Qgrade: "\<And>u. u \<in> biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u = int k"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "\<exists>f g::'k poly. P=op_comp (op_poly_eval euler_yx f) (y_op ^^ k) \<and>
    Q=op_comp (op_poly_eval euler_yx g) (x_op ^^ k) \<and> k=1 \<and> degree f=0 \<and> degree g=0"
proof -
  obtain f where Pf: "P=op_comp (op_poly_eval euler_yx f) (y_op ^^ k)"
    using grade_neg_representation[OF P Pgrade] by blast
  obtain g where Qg: "Q=op_comp (op_poly_eval euler_yx g) (x_op ^^ k)"
    using grade_nat_representation[OF Q Qgrade] by blast
  have normal_exact: "op_comp (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) -
    op_comp (op_comp (op_poly_eval euler_yx f) (y_op ^^ k)) (op_comp (op_poly_eval euler_yx g) (x_op ^^ k)) = id"
    using exact by (simp only: Pf Qg)
  have difference: "g*fallingFactorialPoly k*pcompose f [:-of_nat k,1:] -
    pcompose (g*fallingFactorialPoly k*pcompose f [:-of_nat k,1:]) [:of_nat k,1:] = 1"
    using opposite_grade_normal_forms_commutator_eq_scalar[OF normal_exact] by (simp add: mult_ac)
  have gn: "g \<noteq> 0" and fn: "pcompose f [:-of_nat k,1:] \<noteq> 0"
    using difference by auto
  have rigid: "degree g=0 \<and> k=1 \<and> degree (pcompose f [:-of_nat k,1:])=0"
    by (rule fallingFactorial_shift_difference_forces_generator_case[OF positive gn fn difference])
  have fdegree: "degree f=0" using rigid by (simp add: degree_pcompose)
  show ?thesis by (rule exI[of _ f], rule exI[of _ g]) (use Pf Qg rigid fdegree in auto)
qed

end
