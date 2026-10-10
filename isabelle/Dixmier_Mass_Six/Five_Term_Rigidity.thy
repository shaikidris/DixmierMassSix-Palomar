theory Five_Term_Rigidity
  imports Support_Subset_Products "Sparse_Root_Order"
begin

lemma eq_of_five_terms:
  fixes S :: "'a::field_char_0 poly"
  assumes h5: "termCount S = 5" and h0: "coeff S 0 \<noteq> 0"
    and hrig: "\<And>z :: 'a. (\<And>n. n \<in> sparse_support S \<Longrightarrow> z ^ n = 1) \<Longrightarrow> z = 1"
    and hb: "b \<noteq> 0"
    and ha4: "([:0,1:] - [:a:]) ^ 4 dvd S"
    and hb4: "([:0,1:] - [:b:]) ^ 4 dvd S"
  shows "a = b"
proof -
  have h0s: "0 \<in> sparse_support S" using h0 by simp
  have key: "\<And>n. n \<in> sparse_support S \<Longrightarrow> a ^ n = b ^ n"
  proof -
    fix n
    assume hn: "n \<in> sparse_support S"
    show "a ^ n = b ^ n"
    proof (cases "n=0")
      case True
      then show ?thesis by simp
    next
      case False
      let ?U = "{0,n}"
      let ?T = "sparse_support S - ?U"
      let ?g = "testPoly ?T :: 'a poly"
      have sub: "?U \<subseteq> sparse_support S" using h0s hn by blast
      have fin: "finite ?T" by simp
      have card: "card ?T = 3"
        using h5 False sub
        by (simp add: termCount_def card_Diff_subset)
      have deg: "degree ?g < 4"
        using natDegree_testPoly_le[OF fin, where 'a='a] card by linarith
      have evalnz: "poly ?g (of_nat n) \<noteq> 0"
        by (rule eval_testPoly_ne_zero[OF fin]) simp
      have reduce: "\<And>x :: 'a. (\<Sum>m\<in>sparse_support S.
          coeff S m * x ^ m * poly ?g (of_nat m)) =
        coeff S 0 * poly ?g 0 + coeff S n * x ^ n * poly ?g (of_nat n)"
      proof -
        fix x :: 'a
        have "(\<Sum>m\<in>sparse_support S. coeff S m * x ^ m * poly ?g (of_nat m)) =
            (\<Sum>m\<in>?U. coeff S m * x ^ m * poly ?g (of_nat m))"
          by (rule sum_testPoly_sdiff[OF finite_sparse_support sub])
        also have "... = coeff S 0 * poly ?g 0 + coeff S n * x ^ n * poly ?g (of_nat n)"
          using False by simp
        finally show "(\<Sum>m\<in>sparse_support S. coeff S m * x ^ m * poly ?g (of_nat m)) =
          coeff S 0 * poly ?g 0 + coeff S n * x ^ n * poly ?g (of_nat n)" .
      qed
      have ma: "coeff S 0 * poly ?g 0 + coeff S n * a ^ n * poly ?g (of_nat n) = 0"
        using moment_eq_zero[OF ha4 deg] by (simp only: reduce)
      have mb: "coeff S 0 * poly ?g 0 + coeff S n * b ^ n * poly ?g (of_nat n) = 0"
        using moment_eq_zero[OF hb4 deg] by (simp only: reduce)
      have eq: "coeff S n * a ^ n * poly ?g (of_nat n) = coeff S n * b ^ n * poly ?g (of_nat n)"
        using ma mb by (metis add_left_cancel)
      show ?thesis using eq evalnz hn by simp
    qed
  qed
  have ratio: "a / b = 1"
  proof (rule hrig)
    fix n
    assume "n \<in> sparse_support S"
    then show "(a / b) ^ n = 1" using hb key[of n] by (simp add: power_divide)
  qed
  then show ?thesis using hb by simp
qed

end
