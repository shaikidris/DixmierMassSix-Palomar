theory Ramified_PBW_Reconstruction
  imports Ramified_PBW_Right_Shift
begin
lemma ramified_pbw_reconstruct:
  assumes "0<l" "T\<in>ramified_operator_algebra l"
  shows "(\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j) j)=T"
  using ramified_pbw_coeffs_eval[OF assms]
  by (simp only: ramified_normal_eval_def ramified_pbw_atom_def)

lemma laurent_comp_finite_double_sum:
  assumes "finite S" "finite U" "\<And>j. j\<in>S \<Longrightarrow> laurent_linear (A j)"
  shows "laurent_comp (\<Sum>j\<in>S. A j) (\<Sum>k\<in>U. B k)=
    (\<Sum>j\<in>S. \<Sum>k\<in>U. laurent_comp (A j) (B k))"
  by (simp only: laurent_comp_sum_left[OF assms(1)]; rule sum.cong[OF refl])
     (use assms(2,3) in \<open>auto intro: laurent_comp_sum_right\<close>)

lemma laurent_commutator_finite_double_sum:
  assumes "finite S" "finite U"
    "\<And>j. j\<in>S \<Longrightarrow> laurent_linear (A j)"
    "\<And>k. k\<in>U \<Longrightarrow> laurent_linear (B k)"
  shows "laurent_comp (\<Sum>j\<in>S. A j) (\<Sum>k\<in>U. B k)-
    laurent_comp (\<Sum>k\<in>U. B k) (\<Sum>j\<in>S. A j)=
    (\<Sum>j\<in>S. \<Sum>k\<in>U. laurent_comp (A j) (B k)-laurent_comp (B k) (A j))"
proof -
  have forward: "laurent_comp (\<Sum>j\<in>S. A j) (\<Sum>k\<in>U. B k)=
    (\<Sum>j\<in>S. \<Sum>k\<in>U. laurent_comp (A j) (B k))"
    by (rule laurent_comp_finite_double_sum[OF assms(1,2,3)])
  have backward: "laurent_comp (\<Sum>k\<in>U. B k) (\<Sum>j\<in>S. A j)=
    (\<Sum>j\<in>S. \<Sum>k\<in>U. laurent_comp (B k) (A j))"
    by (simp only: laurent_comp_finite_double_sum[OF assms(2,1,4)]) (rule sum.swap)
  show ?thesis by (simp only: forward backward sum_subtractf)
qed

lemma ramified_pbw_commutator_double_sum:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
  shows "laurent_comp P Q-laurent_comp Q P=
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
      \<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
       laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)-
       laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j))"
proof -
  let ?A = "\<lambda>j. ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j"
  let ?B = "\<lambda>k. ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k"
  have identity: "laurent_comp (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P). ?A j)
      (\<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q). ?B k)-
    laurent_comp (\<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q). ?B k)
      (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P). ?A j)=
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      laurent_comp (?A j) (?B k)-laurent_comp (?B k) (?A j))"
    by (intro laurent_commutator_finite_double_sum Poly_Mapping.finite_keys
      ramified_operator_algebra_linear[where l=l] ramified_pbw_atom_carrier)
  show ?thesis using identity by (simp only: ramified_pbw_reconstruct[OF assms(1,2)]
    ramified_pbw_reconstruct[OF assms(1,3)])
qed

lemma ramified_algebra_finset_sum:
  assumes "finite S" "\<And>j. j\<in>S \<Longrightarrow> F j\<in>ramified_operator_algebra l"
  shows "sum F S\<in>ramified_operator_algebra l"
  using assms by (induction S rule: finite_induct)
    (auto simp: ramified_operator_algebra_def intro: laurent_adjoin_zero laurent_adjoin.add)

lemma ramified_pbw_coeffs_finset_sum:
  assumes "0<l" "finite S" "\<And>j. j\<in>S \<Longrightarrow> F j\<in>ramified_operator_algebra l"
  shows "ramified_pbw_coeffs l (sum F S)=(\<Sum>j\<in>S. ramified_pbw_coeffs l (F j))"
proof -
  have eval: "ramified_normal_eval l (\<Sum>j\<in>S. ramified_pbw_coeffs l (F j))=sum F S"
  proof -
    have expanded: "ramified_normal_eval l (\<Sum>j\<in>S. ramified_pbw_coeffs l (F j))=
      (\<Sum>j\<in>S. ramified_normal_eval l (ramified_pbw_coeffs l (F j)))"
      by (rule ramified_normal_eval_sum[OF assms(2)])
    show ?thesis unfolding expanded by (rule sum.cong[OF refl])
      (intro ramified_pbw_coeffs_eval[OF assms(1)] assms(3); assumption)
  qed
  show ?thesis by (rule ramified_pbw_coeffs_eq_of_eval[OF assms(1)
    ramified_algebra_finset_sum[OF assms(2,3)] eval])
qed

lemma ramified_pbw_coeffs_double_sum:
  assumes "0<l" "finite S" "finite U"
    "\<And>j k. j\<in>S \<Longrightarrow> k\<in>U \<Longrightarrow> F j k\<in>ramified_operator_algebra l"
  shows "ramified_pbw_coeffs l (\<Sum>j\<in>S. \<Sum>k\<in>U. F j k)=
    (\<Sum>j\<in>S. \<Sum>k\<in>U. ramified_pbw_coeffs l (F j k))"
proof -
  have inner: "\<And>j. j\<in>S \<Longrightarrow> (\<Sum>k\<in>U. F j k)\<in>ramified_operator_algebra l"
    by (intro ramified_algebra_finset_sum[OF assms(3)] assms(4)) assumption+
  show ?thesis by (simp only: ramified_pbw_coeffs_finset_sum[OF assms(1,2) inner];
    rule sum.cong[OF refl]; intro ramified_pbw_coeffs_finset_sum[OF assms(1,3)] assms(4); assumption+)
qed

lemma ramified_pbw_coeffs_commutator_double_sum:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l (laurent_comp P Q-laurent_comp Q P)) m=
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      Poly_Mapping.lookup (ramified_pbw_coeffs l
       (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)-
        laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j))) m)"
proof -
  have data: "ramified_pbw_coeffs l (laurent_comp P Q-laurent_comp Q P)=
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>k\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      ramified_pbw_coeffs l
       (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)-
        laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) k) k)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) j) j)))"
    by (subst ramified_pbw_commutator_double_sum[OF assms])
       (intro ramified_pbw_coeffs_double_sum[OF assms(1)] Poly_Mapping.finite_keys
        ramified_algebra_diff ramified_algebra_comp ramified_pbw_atom_carrier)
  show ?thesis using arg_cong[OF data, where f="\<lambda>a. Poly_Mapping.lookup a m"]
    by (simp only: Poly_Mapping.lookup_sum)
qed
end
