theory Six_Node_Moment_Kernel
  imports Triple_Set_Helpers
begin

lemma exists_affine_of_moments:
  fixes w :: "nat \<Rightarrow> 'a::field_char_0"
  assumes fin: "finite N" and hN: "card N = 6" and h0: "0 \<in> N"
    and hw: "\<And>g :: 'a poly. degree g < 4 \<Longrightarrow>
      (\<Sum>m\<in>N. w m * poly g (of_nat m)) = 0"
  shows "\<exists>A B :: 'a. \<forall>n\<in>N.
    w n * (\<Prod>m\<in>N-{n}. (of_nat n - of_nat m)) = A + B * of_nat n"
proof -
  have notsub: "\<not> N \<subseteq> {0}"
  proof
    assume sub0: "N \<subseteq> {0}"
    have "card N \<le> card {0::nat}" by (rule card_mono) (simp_all add: sub0)
    with hN show False by simp
  qed
  then obtain n1 where hn1: "n1 \<in> N" and hn10: "n1 \<noteq> 0" by blast
  have nz: "(of_nat n1 :: 'a) \<noteq> 0" using hn10 by simp
  let ?D = "\<lambda>n. (\<Prod>m\<in>N-{n}. (of_nat n - of_nat m :: 'a))"
  let ?A = "w 0 * ?D 0"
  let ?B = "(w n1 * ?D n1 - ?A) / of_nat n1"
  have Bn: "?B * of_nat n1 = w n1 * ?D n1 - ?A"
    using nz by simp
  have affine: "\<And>n. n \<in> N \<Longrightarrow> w n * ?D n = ?A + ?B * of_nat n"
  proof -
    fix n
    assume hn: "n \<in> N"
    show "w n * ?D n = ?A + ?B * of_nat n"
    proof (cases "n=0")
      case True
      then show ?thesis by simp
    next
      case n0: False
      show ?thesis
      proof (cases "n=n1")
        case True
        then show ?thesis using Bn by simp
      next
        case nn1: False
        let ?U = "{0,n1,n}"
        let ?T = "N-?U"
        let ?g = "testPoly ?T :: 'a poly"
        have sub: "?U \<subseteq> N" using h0 hn1 hn by blast
        have finiteT: "finite ?T" using fin by simp
        have cardU: "card ?U = 3" using n0 nn1 hn10 by simp
        have cardT: "card ?T = 3" using hN sub cardU
          by (simp add: card_Diff_subset)
        have dg: "degree ?g < 4"
          using natDegree_testPoly_le[OF finiteT, where 'a='a] cardT by linarith
        have rel: "w 0 * poly ?g 0 + w n1 * poly ?g (of_nat n1) + w n * poly ?g (of_nat n) = 0"
        proof -
          have "(\<Sum>m\<in>N. w m * poly ?g (of_nat m)) =
              (\<Sum>m\<in>?U. w m * poly ?g (of_nat m))"
            by (rule sum_testPoly_sdiff[OF fin sub])
          moreover have "(\<Sum>m\<in>?U. w m * poly ?g (of_nat m)) =
              w 0 * poly ?g 0 + w n1 * poly ?g (of_nat n1) + w n * poly ?g (of_nat n)"
            using n0 nn1 hn10 by (simp add: add.assoc)
          ultimately show ?thesis using hw[OF dg] by simp
        qed
        have D0: "?D 0 = poly ?g 0 * ((0 - of_nat n1) * (0 - of_nat n))"
          using prod_erase_eq_eval_testPoly_mul[OF fin sub, of 0, where 'a='a]
            n0 nn1 hn10
          by (simp add: erase_triple_fst)
        have D1: "?D n1 = poly ?g (of_nat n1) *
            (of_nat n1 * (of_nat n1 - of_nat n))"
          using prod_erase_eq_eval_testPoly_mul[OF fin sub, of n1, where 'a='a]
            n0 nn1 hn10
          by (simp add: erase_triple_snd)
        have Dn: "?D n = poly ?g (of_nat n) *
            (of_nat n * (of_nat n - of_nat n1))"
          using prod_erase_eq_eval_testPoly_mul[OF fin sub, of n, where 'a='a]
            n0 nn1 hn10
          by (simp add: erase_triple_thd)
        have identity: "of_nat n1 * (w n * ?D n) -
              (of_nat n1 * ?A + (w n1 * ?D n1 - ?A) * of_nat n) =
            of_nat n1 * of_nat n * (of_nat n - of_nat n1) *
              (w 0 * poly ?g 0 + w n1 * poly ?g (of_nat n1) + w n * poly ?g (of_nat n))"
          unfolding D0 D1 Dn by algebra
        have key: "of_nat n1 * (w n * ?D n) =
            of_nat n1 * ?A + (w n1 * ?D n1 - ?A) * of_nat n"
          using identity rel by simp
        have "of_nat n1 * (w n * ?D n - (?A + ?B * of_nat n)) =
            (of_nat n1 * (w n * ?D n) -
              (of_nat n1 * ?A + (w n1 * ?D n1 - ?A) * of_nat n)) +
              of_nat n * ((w n1 * ?D n1 - ?A) - ?B * of_nat n1)"
          by algebra
        also have "... = 0" by (simp only: key Bn; simp)
        finally show ?thesis using nz by simp
      qed
    qed
  qed
  show ?thesis by (rule exI[of _ ?A], rule exI[of _ ?B], rule ballI, rule affine, assumption)
qed

end
