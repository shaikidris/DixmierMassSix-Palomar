theory Joseph_Local_Nilpotence
  imports Joseph_Commutator_Chain
begin

lemma joseph_chain_mul_termination_bound:
  fixes P R S :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
    and hR: "josephCommutatorChain P R n=0" and hS: "josephCommutatorChain P S m=0"
  shows "josephCommutatorChain P (op_comp R S) (n+m)=0"
proof -
  have Pl: "poly_linear P" by (rule weyl_linear[OF P])
  have all: "\<forall>n m R S. n+m=k \<longrightarrow> R\<in>weyl_algebra \<longrightarrow> S\<in>weyl_algebra \<longrightarrow>
      josephCommutatorChain P R n=0 \<longrightarrow> josephCommutatorChain P S m=0 \<longrightarrow>
      josephCommutatorChain P (op_comp R S) (n+m)=0" for k
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (intro allI impI)
      fix n m and R S :: "complex poly_operator"
      assume index: "n+m=k" and R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
        and rn: "josephCommutatorChain P R n=0" and sm: "josephCommutatorChain P S m=0"
      have Rl: "poly_linear R" by (rule weyl_linear[OF R])
      show "josephCommutatorChain P (op_comp R S) (n+m)=0"
      proof (cases n)
        case 0
        have rzero: "R=0" using rn by (simp add: 0)
        have product_zero: "op_comp R S=(0::complex poly_operator)"
          by (rule ext) (simp only: op_comp_def rzero zero_fun_def)
        show ?thesis by (simp only: product_zero joseph_chain_zero[OF Pl])
      next
        case (Suc a)
        show ?thesis
        proof (cases m)
          case 0
          have szero: "S=0" using sm by (simp add: 0)
          have product_zero: "op_comp R S=(0::complex poly_operator)"
            by (rule ext) (simp only: op_comp_def szero zero_fun_def poly_linear_zero_image[OF Rl])
          show ?thesis by (simp only: product_zero joseph_chain_zero[OF Pl])
        next
          case (Suc b)
          let ?DR = "op_comp P R-op_comp R P"
          let ?DS = "op_comp P S-op_comp S P"
          have DR: "?DR\<in>weyl_algebra" and DS: "?DS\<in>weyl_algebra"
            using P R S unfolding weyl_algebra_def by (auto intro: op_adjoin.diff op_adjoin.comp)
          have drn: "josephCommutatorChain P ?DR a=0" using rn
            by (simp only: joseph_chain_shift \<open>n=Suc a\<close>)
          have dsm: "josephCommutatorChain P ?DS b=0" using sm
            by (simp only: joseph_chain_shift \<open>m=Suc b\<close>)
          have lt_left: "a+Suc b<k" using index \<open>n=Suc a\<close> \<open>m=Suc b\<close> by arith
          have lt_right: "Suc a+b<k" using index \<open>n=Suc a\<close> \<open>m=Suc b\<close> by arith
          have rn_suc: "josephCommutatorChain P R (Suc a)=0" using rn by (simp only: \<open>n=Suc a\<close>)
          have sm_suc: "josephCommutatorChain P S (Suc b)=0" using sm by (simp only: \<open>m=Suc b\<close>)
          have left: "josephCommutatorChain P (op_comp ?DR S) (a+Suc b)=0"
            by (rule less.IH[OF lt_left, rule_format, of a "Suc b" ?DR S, OF refl DR S drn sm_suc])
          have right: "josephCommutatorChain P (op_comp R ?DS) (Suc a+b)=0"
            by (rule less.IH[OF lt_right, rule_format, of "Suc a" b R ?DS, OF refl R DS rn_suc dsm])
          have same_index: "a+Suc b=Suc a+b" by arith
          have right': "josephCommutatorChain P (op_comp R ?DS) (a+Suc b)=0"
            by (simp only: same_index right)
          have leibniz: "op_comp P (op_comp R S)-op_comp (op_comp R S) P=
            op_comp ?DR S+op_comp R ?DS"
            by (rule ext) (simp add: op_comp_def joseph_linear_diff_image[OF Rl]; algebra)
          have k: "n+m=Suc (a+Suc b)" using \<open>n=Suc a\<close> \<open>m=Suc b\<close> by arith
          show ?thesis by (simp only: k joseph_chain_shift[symmetric] leibniz joseph_chain_add[OF Pl]
            left right' add_0)
        qed
      qed
    qed
  qed
  show ?thesis by (rule all[of "n+m", rule_format, of n m R S, OF refl R S hR hS])
qed

lemma joseph_chain_terminates_on_adjoin:
  fixes P Q R :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and R: "R\<in>op_adjoin {P,Q}"
  shows "\<exists>n. josephCommutatorChain P R n=0"
proof -
  have Pl: "poly_linear P" by (rule weyl_linear[OF P])
  have carrier: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
    by (rule weyl_nested_adjoin) (use P Q in auto)
  have extend: "josephCommutatorChain P T (n+m)=0" if "josephCommutatorChain P T m=0" for T n m
    by (simp only: joseph_chain_comp that joseph_chain_zero[OF Pl])
  show ?thesis using R
  proof (induction rule: op_adjoin.induct)
    case (generator T)
    have p: "josephCommutatorChain P P 1=0" by simp
    have neg_exact: "-(op_comp Q P-op_comp P Q)= -id" using exact by (rule arg_cong)
    have reverse: "op_comp P Q-op_comp Q P= -id" using neg_exact by (simp only: minus_diff_eq)
    have q: "josephCommutatorChain P Q 2=0"
      by (simp only: numeral_2_eq_2 josephCommutatorChain.simps reverse)
        (simp add: op_comp_def fun_eq_iff joseph_linear_neg_image[OF Pl] poly_linear_zero_image[OF Pl])
    have alternatives: "T=P \<or> T=Q" using generator.hyps by simp
    show ?case
    proof (cases "T=P")
      case True
      show ?thesis by (rule exI[of _ 1]) (simp only: True p)
    next
      case False
      have tq: "T=Q" using alternatives False by blast
      show ?thesis by (rule exI[of _ 2]) (simp only: tq q)
    qed
  next
    case (scalar c)
    have "josephCommutatorChain P (op_scalar c) 1=0"
      using Pl by (auto simp: op_comp_def op_scalar_def fun_eq_iff poly_linear_def)
    then show ?case by blast
  next
    case (add T U)
    obtain n m where n: "josephCommutatorChain P T n=0" and m: "josephCommutatorChain P U m=0"
      using add.IH by blast
    have tn: "josephCommutatorChain P T (n+m)=0" using extend[OF n, of m] by (simp add: add.commute)
    have um: "josephCommutatorChain P U (n+m)=0" by (rule extend[OF m])
    show ?case by (intro exI[of _ "n+m"]) (simp only: joseph_chain_add[OF Pl] tn um add_0)
  next
    case (diff T U)
    obtain n m where n: "josephCommutatorChain P T n=0" and m: "josephCommutatorChain P U m=0"
      using diff.IH by blast
    have tn: "josephCommutatorChain P T (n+m)=0" using extend[OF n, of m] by (simp add: add.commute)
    have um: "josephCommutatorChain P U (n+m)=0" by (rule extend[OF m])
    show ?case by (intro exI[of _ "n+m"]) (simp only: joseph_chain_diff[OF Pl] tn um diff_self)
  next
    case (comp T U)
    obtain n m where n: "josephCommutatorChain P T n=0" and m: "josephCommutatorChain P U m=0"
      using comp.IH by blast
    have T: "T\<in>weyl_algebra" and U: "U\<in>weyl_algebra" using comp.hyps carrier by blast+
    show ?case by (intro exI[of _ "n+m"]) (rule joseph_chain_mul_termination_bound[OF P T U n m])
  qed
qed

lemma joseph_two_bracket_of_generated_nonzero_bracket:
  fixes P Q R :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and weight: "0<rho+sigma"
    and adjoin: "R\<in>op_adjoin {P,Q}"
    and first: "biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0"
  shows "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and>
    biv_poisson (leading_form rho sigma P) (leading_form rho sigma T)\<noteq>0 \<and>
    biv_poisson (leading_form rho sigma P)
      (biv_poisson (leading_form rho sigma P) (leading_form rho sigma T))=0"
  by (rule joseph_two_bracket_of_terminating_chain[OF P R weight adjoin first
    joseph_chain_terminates_on_adjoin[OF P Q exact adjoin]])

end
