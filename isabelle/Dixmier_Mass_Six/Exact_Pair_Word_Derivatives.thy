theory Exact_Pair_Word_Derivatives
  imports "Polynomial_Endomorphisms"
begin

lemma exact_word_linear_add_image:
  "poly_linear T \<Longrightarrow> T (p+q)=T p+T q"
  unfolding poly_linear_def by blast
lemma exact_word_linear_smult_image:
  "poly_linear T \<Longrightarrow> T (smult c p)=smult c (T p)"
  unfolding poly_linear_def by blast

lemma exact_word_linear_diff_image:
  assumes "poly_linear T"
  shows "T (p-q)=T p-T q"
proof -
  have scalar: "T (smult (-1) q)=smult (-1) (T q)"
    using assms unfolding poly_linear_def by blast
  have negative: "T (-q)= -T q" using scalar by simp
  show ?thesis by (simp only: diff_conv_add_uminus exact_word_linear_add_image[OF assms] negative)
qed

lemma commutator_one_power_succ:
  fixes U V :: "complex poly_operator"
  assumes V: "poly_linear V"
    and exact: "op_comp U V-op_comp V U=id"
  shows "op_comp U (V^^Suc n)-op_comp (V^^Suc n) U =
    (\<lambda>p. smult (of_nat (Suc n)) ((V^^n) p))"
proof -
  have recurrence: "U (V p)=V (U p)+p" for p
    using fun_cong[OF exact, of p] by (simp add: op_comp_def minus_apply diff_eq_eq add.commute)
  have equation: "U ((V^^Suc n) p)=(V^^Suc n) (U p)+smult (of_nat (Suc n)) ((V^^n) p)" for p
  proof (induction n arbitrary: p)
    case 0
    show ?case using recurrence[of p] by simp
  next
    case (Suc n)
    have step: "U (V ((V^^Suc n) p))=V (U ((V^^Suc n) p))+(V^^Suc n) p"
      by (rule recurrence)
    have bump: "smult (of_nat (Suc n)+1) t=smult (of_nat (Suc n)) t+t" for t :: "complex poly"
      by (simp only: smult_add_left smult_1_left)
    have stage: "U (V ((V^^Suc n) p))=V ((V^^Suc n) (U p))+
      smult (of_nat (Suc n)) (V ((V^^n) p))+(V^^Suc n) p"
      by (simp only: step Suc.IH exact_word_linear_add_image[OF V] exact_word_linear_smult_image[OF V])
    show ?case
      using stage by (simp only: funpow.simps(2) comp_apply of_nat_Suc
        smult_add_left smult_1_left add.assoc add.commute add.left_commute)
  qed
  show ?thesis by (rule ext) (simp only: op_comp_def minus_apply equation; simp)
qed

lemma exact_pair_commutator_Q_word:
  fixes P Q :: "complex poly_operator"
  assumes P: "poly_linear P"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "op_comp Q (op_comp (P^^Suc i) (Q^^j))-
    op_comp (op_comp (P^^Suc i) (Q^^j)) Q =
    (\<lambda>p. smult (of_nat (Suc i)) (op_comp (P^^i) (Q^^j) p))"
proof -
  have powers: "Q ((Q^^j) p)=(Q^^j) (Q p)" for p
    by (simp add: funpow_swap1)
  have transport: "Q ((P^^Suc i) r)-(P^^Suc i) (Q r)=smult (of_nat (Suc i)) ((P^^i) r)" for r
    using fun_cong[OF commutator_one_power_succ[OF P exact, where n=i], of r]
    by (simp add: op_comp_def)
  show ?thesis by (rule ext) (simp only: op_comp_def fun_diff_def powers[symmetric] transport)
qed


lemma commutator_neg_one_power_succ:
  fixes U V :: "complex poly_operator"
  assumes V: "poly_linear V"
    and exact: "op_comp U V-op_comp V U= -id"
  shows "op_comp U (V^^Suc n)-op_comp (V^^Suc n) U =
    (\<lambda>p. -smult (of_nat (Suc n)) ((V^^n) p))"
proof -
  have recurrence: "U (V p)=V (U p)-p" for p
    using fun_cong[OF exact, of p] by (simp add: op_comp_def minus_apply uminus_apply diff_eq_eq eq_diff_eq add.commute)
  have equation: "U ((V^^Suc n) p)=(V^^Suc n) (U p)-smult (of_nat (Suc n)) ((V^^n) p)" for p
  proof (induction n arbitrary: p)
    case 0
    show ?case using recurrence[of p] by simp
  next
    case (Suc n)
    have step: "U (V ((V^^Suc n) p))=V (U ((V^^Suc n) p))-(V^^Suc n) p"
      by (rule recurrence)
    have bump: "smult (of_nat (Suc n)+1) t=smult (of_nat (Suc n)) t+t" for t :: "complex poly"
      by (simp only: smult_add_left smult_1_left)
    have stage: "U (V ((V^^Suc n) p))=V ((V^^Suc n) (U p))-
      smult (of_nat (Suc n)) (V ((V^^n) p))-(V^^Suc n) p"
      by (simp only: step Suc.IH exact_word_linear_diff_image[OF V] exact_word_linear_smult_image[OF V])
    show ?case
      using stage by (simp only: funpow.simps(2) comp_apply of_nat_Suc
        smult_add_left smult_1_left diff_diff_add add.assoc add.commute add.left_commute)
  qed
  show ?thesis by (rule ext) (simp only: op_comp_def minus_apply equation; simp)
qed

lemma exact_pair_commutator_P_word:
  fixes P Q :: "complex poly_operator"
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "op_comp P (op_comp (P^^i) (Q^^Suc j))-
    op_comp (op_comp (P^^i) (Q^^Suc j)) P =
    (\<lambda>p. -smult (of_nat (Suc j)) (op_comp (P^^i) (Q^^j) p))"
proof -
  have reverse: "op_comp P Q-op_comp Q P= -id"
    using arg_cong[OF exact, where f="\<lambda>T. -T"] by simp
  have transport: "P ((Q^^Suc j) r)-(Q^^Suc j) (P r)= -smult (of_nat (Suc j)) ((Q^^j) r)" for r
    using fun_cong[OF commutator_neg_one_power_succ[OF Q reverse, where n=j], of r]
    by (simp add: op_comp_def)
  have powers: "P ((P^^i) r)=(P^^i) (P r)" for r by (simp add: funpow_swap1)
  have linear: "poly_linear (P^^i)" by (rule poly_linear_power[OF P])
  show ?thesis
  proof (rule ext)
    fix p
    have "P ((P^^i) ((Q^^Suc j) p))-(P^^i) ((Q^^Suc j) (P p))=
      (P^^i) (P ((Q^^Suc j) p)-(Q^^Suc j) (P p))"
      by (simp only: powers exact_word_linear_diff_image[OF linear])
    also have "...= -smult (of_nat (Suc j)) ((P^^i) ((Q^^j) p))"
    proof -
      have scalar: "(P^^i) (smult (-of_nat (Suc j)) ((Q^^j) p))=
        smult (-of_nat (Suc j)) ((P^^i) ((Q^^j) p))"
        using linear unfolding poly_linear_def by blast
      show ?thesis
        by (simp only: transport smult_minus_left[symmetric] scalar)
    qed
    finally show "(op_comp P (op_comp (P^^i) (Q^^Suc j))-
      op_comp (op_comp (P^^i) (Q^^Suc j)) P) p=
      (\<lambda>p. -smult (of_nat (Suc j)) (op_comp (P^^i) (Q^^j) p)) p"
      by (simp only: op_comp_def fun_diff_def)
  qed
qed

end
