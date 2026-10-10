theory Generator_Centralizer
  imports "PBW_Finite_Coordinates"
begin

declare id_def [simp del]

lemma normal_monomial_comp_y:
  "op_comp (normal_monomial i j) y_op = (normal_monomial i (Suc j) :: 'k::field poly_operator)"
  by (rule ext) (simp add: op_comp_def normal_monomial_apply y_op_def funpow_Suc_right funpow_swap1)

lemma yOp_commutator_normalOrderedMonomial:
  "op_comp y_op (normal_monomial i j) - op_comp (normal_monomial i j) y_op =
    (\<lambda>p. smult (of_nat i) (normal_monomial (i-1) j p))"
  by (simp only: y_normal_monomial normal_monomial_comp_y add_diff_cancel_right')

lemma pbwCoeff_finset_sum:
  fixes F :: "nat \<times> nat \<Rightarrow> 'k::field_char_0 poly_operator"
  assumes "finite S"
  shows "pbw_coeff (\<Sum>u\<in>S. F u) i j = (\<Sum>u\<in>S. pbw_coeff (F u) i j)"
proof -
  have z: "pbw_coeff (0::'k poly_operator) i j=0" by (simp add: pbw_coeff_def)
  show ?thesis using assms
  proof (induction S)
    case empty show ?case by (simp only: sum.empty z)
  next
    case (insert x S)
    show ?case by (simp only: sum.insert[OF insert.hyps] pbw_coeff_add insert.IH)
  qed
qed

lemma centralizer_sum_apply:
  "(\<Sum>u\<in>S. F u) p = (\<Sum>u\<in>S. F u p :: 'k::field poly)"
  by (induction S rule: infinite_finite_induct) auto

lemma centralizer_finite_sum_as_operators:
  "finite_normal_sum S c = (\<Sum>u\<in>S. (\<lambda>p. smult (c u) (normal_monomial (fst u) (snd u) p)))"
  by (rule ext) (simp add: finite_normal_sum_def centralizer_sum_apply)

lemma centralizer_commutator_expansion:
  "op_comp y_op (finite_normal_sum S c) - op_comp (finite_normal_sum S c) y_op =
   (\<Sum>u\<in>S. (\<lambda>p. smult (c u * of_nat (fst u)) (normal_monomial (fst u-1) (snd u) p)))"
proof -
  have mon: "y_op (normal_monomial a b p) - normal_monomial a b (y_op p) =
      smult (of_nat a) (normal_monomial (a-1) b p)" for a b p
    using fun_cong[OF yOp_commutator_normalOrderedMonomial[of a b], of p]
    by (simp only: op_comp_def minus_apply)
  have ds: "pderiv (\<Sum>u\<in>A. f u) = (\<Sum>u\<in>A. pderiv (f u))" for A f
    using higher_pderiv_sum[where n=1 and f=f and A=A] by simp
  show ?thesis
    by (rule ext) (simp add: op_comp_def finite_normal_sum_def y_op_def ds
      pderiv_smult sum_subtractf[symmetric] smult_diff_right[symmetric] mon[unfolded y_op_def] smult_smult centralizer_sum_apply)
qed

lemma yOp_commutator_pbwCoeff:
  fixes R :: "'k::field_char_0 poly_operator"
  assumes hR: "R \<in> weyl_algebra"
  shows "pbw_coeff (op_comp y_op R - op_comp R y_op) i j =
    of_nat (Suc i) * pbw_coeff R (Suc i) j"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "finite_normal_sum {u. c u \<noteq> 0} c = R"
    using weyl_exists_finite_coordinates[OF hR] by blast
  let ?S = "{u. c u \<noteq> 0}"
  have coeff: "pbw_coeff R (Suc i) j = c (Suc i,j)"
    unfolding rep[symmetric] by (rule pbw_coeff_finite_coordinates[OF fin])
  have shift: "pbw_coeff (op_comp y_op R-op_comp R y_op) i j =
    (\<Sum>u\<in>?S. c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0))"
    unfolding rep[symmetric] centralizer_commutator_expansion
    by (simp only: pbwCoeff_finset_sum[OF fin] pbw_coeff_smult pbw_coeff_normal_monomial)
  have off: "c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0) = (0::'k)"
    if "u \<noteq> (Suc i,j)" for u
  proof (cases "fst u=0")
    case True then show ?thesis by simp
  next
    case False
    have hnot: "\<not>(i=fst u-1 \<and> j=snd u)" using that False by (cases u) auto
    show ?thesis by (simp only: hnot if_False mult_zero_right)
  qed
  have sum: "(\<Sum>u\<in>?S. c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0)) = c (Suc i,j) * of_nat (Suc i)"
  proof (cases "(Suc i,j) \<in> ?S")
    case True
    have delta: "c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0) =
      (if u=(Suc i,j) then c (Suc i,j)*of_nat (Suc i) else 0)" for u
    proof (cases "u=(Suc i,j)")
      case True then show ?thesis by simp
    next
      case False
      show ?thesis using off[OF False] by (simp only: False if_False)
    qed
    show ?thesis using True by (simp only: delta sum.delta[OF fin] True if_True)
  next
    case False
    have z: "c (Suc i,j)=0" using False by simp
    have "(\<Sum>u\<in>?S. c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0)) = 0"
    proof (rule sum.neutral, rule ballI)
      fix u assume hu: "u \<in> ?S"
      have ne: "u \<noteq> (Suc i,j)" using hu False by auto
      show "c u * of_nat (fst u) * (if i=fst u-1 \<and> j=snd u then 1 else 0)=0"
        by (rule off[OF ne])
    qed
    then show ?thesis by (simp add: z)
  qed
  show ?thesis using shift sum by (simp only: coeff mult.commute)
qed

lemma pbwCoeff_pos_x_eq_zero_of_commutes_y:
  fixes R :: "'k::field_char_0 poly_operator"
  assumes "R \<in> weyl_algebra" "op_comp y_op R-op_comp R y_op=0"
  shows "pbw_coeff R (Suc i) j=0"
proof -
  have z: "pbw_coeff (0::'k poly_operator) i j=0" by (simp add: pbw_coeff_def)
  have nz: "(of_nat (Suc i)::'k) \<noteq> 0" by (simp only: of_nat_eq_0_iff)
  have eq: "0=of_nat (Suc i)*pbw_coeff R (Suc i) j"
    using yOp_commutator_pbwCoeff[OF assms(1), of i j]
    by (simp only: assms(2) z)
  from eq nz show ?thesis by (metis mult_eq_0_iff)
qed

lemma mem_adjoin_y_of_commutes_y:
  fixes R :: "'k::field_char_0 poly_operator"
  assumes hR: "R \<in> weyl_algebra" and comm: "op_comp y_op R-op_comp R y_op=0"
  shows "R \<in> op_adjoin {y_op}"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "finite_normal_sum {u. c u \<noteq> 0} c = R"
    using weyl_exists_finite_coordinates[OF hR] by blast
  have support: "fst u=0" if "c u \<noteq> 0" for u
  proof (rule ccontr)
    assume nz: "fst u \<noteq> 0"
    obtain i where i: "fst u=Suc i" using nz by (cases "fst u") auto
    have z: "pbw_coeff R (Suc i) (snd u)=0"
      by (rule pbwCoeff_pos_x_eq_zero_of_commutes_y[OF hR comm])
    have "c u=0" using z
      by (simp add: rep[symmetric] pbw_coeff_finite_coordinates[OF fin] i[symmetric])
    with that show False by contradiction
  qed
  have term_mem: "(\<lambda>p. smult (c u) (normal_monomial (fst u) (snd u) p)) \<in> op_adjoin {y_op}"
    if "u\<in>{u. c u \<noteq> 0}" for u
  proof -
    have zero: "fst u=0" using support that by simp
    have y: "y_op \<in> op_adjoin {y_op}" by (rule op_adjoin.generator) simp
    have "(y_op ^^ snd u) \<in> op_adjoin {y_op}" by (rule op_adjoin_power[OF y])
    then show ?thesis using op_adjoin_smult[of "y_op ^^ snd u" "{y_op}" "c u"]
      by (simp add: zero normal_monomial_def op_comp_def)
  qed
  show ?thesis unfolding rep[symmetric] centralizer_finite_sum_as_operators
    by (rule op_adjoin_sum[OF term_mem])
qed
end
