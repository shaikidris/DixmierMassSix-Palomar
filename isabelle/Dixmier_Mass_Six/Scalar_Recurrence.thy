theory Scalar_Recurrence
  imports "HOL-Computational_Algebra.Polynomial"
begin

fun recSeq :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "recSeq s L 0 = -1"
| "recSeq s L (Suc j) =
    (-(of_nat s * (of_nat L - of_nat j)) * recSeq s L j + (if j=0 then 1 else 0)) /
      (1 + of_nat s * (of_nat j + 1))"

lemma recSeq_succ:
  "recSeq s L (j+1) =
    (-(of_nat s * (of_nat L - of_nat j)) * recSeq s L j + (if j=0 then 1 else 0)) /
      (1 + of_nat s * (of_nat j + 1))"
  by simp

lemma recSeq_sign:
  assumes hs: "1 \<le> s" and hL: "1 \<le> L"
  shows "\<forall>j\<le>L. 0 < (-1 :: real) ^ (j+1) * recSeq s L j"
proof -
  have spos: "0 < s" using hs by arith
  have sr: "(0::real) < of_nat s" using spos by simp
  have sign: "j \<le> L \<longrightarrow> 0 < (-1::real) ^ (j+1) * recSeq s L j" for j
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    show ?case
    proof
      assume hj: "Suc j \<le> L"
      have jle: "j \<le> L" using hj by arith
      have prev: "0 < (-1::real) ^ (j+1) * recSeq s L j" by (rule mp[OF Suc.IH jle])
      have nonneg: "(0::real) \<le> of_nat s * (of_nat j + 1)"
        by (intro mult_nonneg_nonneg) simp_all
      have den: "(0::real) < 1 + of_nat s * (of_nat j + 1)" using nonneg by linarith
      have jl: "j < L" using hj by arith
      have difference: "(0::real) < of_nat L - of_nat j" using jl by simp
      show "0 < (-1::real) ^ (Suc j+1) * recSeq s L (Suc j)"
      proof (cases "j=0")
        case True
        have nonneg': "(0::real) \<le> of_nat s * of_nat L"
          by (intro mult_nonneg_nonneg) simp_all
        have num: "(0::real) < of_nat s * of_nat L + 1" using nonneg' by linarith
        have den0: "(0::real) < 1 + of_nat s" using den True by simp
        have pos: "(0::real) < (of_nat s * of_nat L + 1) / (1 + of_nat s)"
          by (rule divide_pos_pos[OF num den0])
        show ?thesis using pos True by simp
      next
        case False
        let ?u = "of_nat s * (of_nat L - of_nat j) :: real"
        let ?d = "1 + of_nat s * (of_nat j + 1) :: real"
        have recur: "recSeq s L (Suc j) = -?u * recSeq s L j / ?d"
          using False by simp
        have index: "Suc j + 1 = Suc (j+1)" by simp
        have ident: "(-1::real) ^ (Suc j+1) * (-?u * recSeq s L j / ?d) =
            (?u / ?d) * ((-1::real) ^ (j+1) * recSeq s L j)"
          by (simp only: index power_Suc divide_inverse; algebra)
        have pos: "0 < (?u / ?d) * ((-1::real) ^ (j+1) * recSeq s L j)"
          by (rule mult_pos_pos[OF divide_pos_pos[OF mult_pos_pos[OF sr difference] den] prev])
        show ?thesis using pos by (simp only: recur ident)
      qed
    qed
  qed
  show ?thesis using sign by blast
qed

lemma recSeq_eq_zero:
  assumes hL: "1 \<le> L"
  shows "\<forall>j. L < j \<longrightarrow> recSeq s L j = 0"
proof
  fix j
  show "L < j \<longrightarrow> recSeq s L j = 0"
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    show ?case
    proof
      assume hj: "L < Suc j"
      have jnz: "j \<noteq> 0" using hL hj by arith
      show "recSeq s L (Suc j) = 0"
      proof (cases "L < j")
        case True
        have rec: "recSeq s L j = 0" by (rule mp[OF Suc.IH True])
        show ?thesis using jnz by (simp add: rec)
      next
        case False
        have "j=L" using hj False by arith
        then show ?thesis using jnz by simp
      qed
    qed
  qed
qed

end
