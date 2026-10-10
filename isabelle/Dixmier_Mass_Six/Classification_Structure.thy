theory Classification_Structure
  imports "Multiplicity_Transport"
    "Companion_Roots"
begin

lemma structure_multiplicity_pos:
  assumes "p \<noteq> 0"
  shows "0 < rootMultiplicity a p \<longleftrightarrow> poly p a = 0"
  using assms by (simp add: rootMultiplicity_eq_order order_gt_0_iff)

lemma structure_multiplicity_nonroot:
  "poly p a \<noteq> 0 \<Longrightarrow> rootMultiplicity a p = 0"
  by (simp add: rootMultiplicity_def order_0I)

lemma structure_multiplicity_mult:
  assumes "p*q \<noteq> 0"
  shows "rootMultiplicity a (p*q) = rootMultiplicity a p + rootMultiplicity a q"
  using assms by (simp add: rootMultiplicity_eq_order order_mult)

lemma Comp_exists_double_root:
  assumes h: "Comp rho s r f" and hs: "s<rho"
    and hr0: "poly r 0=1" and hr: "0<degree r"
  shows "\<exists>a. 2 \<le> rootMultiplicity a r"
proof (rule ccontr)
  assume neg: "\<not> (\<exists>a. 2 \<le> rootMultiplicity a r)"
  have hf: "0<degree f" by (rule Comp_natDegree_f_pos[OF h hs hr0 hr])
  have rnz: "r\<noteq>0" and fnz: "f\<noteq>0" using hr hf by auto
  have dvd: "r dvd f"
  proof (rule dvd_of_forall_rootMultiplicity_le[OF rnz])
    fix a
    show "rootMultiplicity a r \<le> rootMultiplicity a f"
    proof (cases "poly r a=0")
      case True
      have "poly f a=0" by (rule Comp_isRoot_f[OF h hs hr0 True])
      then have "0<rootMultiplicity a f" using structure_multiplicity_pos[OF fnz] by blast
      moreover have "rootMultiplicity a r < 2" using neg by (meson not_le)
      ultimately show ?thesis by arith
    next
      case False
      then show ?thesis by (simp add: structure_multiplicity_nonroot)
    qed
  qed
  have "degree r \<le> degree f" by (rule dvd_imp_degree_le[OF dvd fnz])
  moreover have "degree f < degree r" by (rule Comp_natDegree_f_lt[OF h hs hr hf])
  ultimately show False by simp
qed

lemma Comp_eq_X_sub_one_mul:
  assumes h: "Comp rho s r f" and hs: "s<rho"
    and hr0: "poly r 0=1" and hr: "0<degree r"
    and h1: "rootMultiplicity 1 r=2"
    and hother: "\<And>a. a\<noteq>1 \<Longrightarrow> rootMultiplicity a r \<le> 1"
  shows "r = [:-1,1:] * f"
proof -
  have hf: "0<degree f" by (rule Comp_natDegree_f_pos[OF h hs hr0 hr])
  have rnz: "r\<noteq>0" and fnz: "f\<noteq>0" using hr hf by auto
  have gnz: "[:-1,1:]*f\<noteq>0" using fnz by (simp add: mult_eq_0_iff del: mult_pCons_left mult_pCons_right)
  have dvd: "r dvd [:-1,1:]*f"
  proof (rule dvd_of_forall_rootMultiplicity_le[OF rnz])
    fix a
    have mult: "rootMultiplicity a ([:-1,1:]*f) =
      rootMultiplicity a [:-1,1:] + rootMultiplicity a f"
      by (rule structure_multiplicity_mult[OF gnz])
    show "rootMultiplicity a r \<le> rootMultiplicity a ([:-1,1:]*f)"
    proof (cases "a=1")
      case True
      have "poly r 1=0" using h1 structure_multiplicity_pos[OF rnz, of 1] by simp
      then have "poly f 1=0" by (rule Comp_isRoot_f[OF h hs hr0])
      then have pos: "0<rootMultiplicity 1 f" using structure_multiplicity_pos[OF fnz] by blast
      have one: "rootMultiplicity 1 ([:-1,1:]::complex poly)=1"
        by (simp add: rootMultiplicity_eq_count_proots proots_linear_factor)
      show ?thesis using True mult pos h1 one by arith
    next
      case False
      have bound: "rootMultiplicity a r \<le> 1" by (rule hother[OF False])
      show ?thesis
      proof (cases "poly r a=0")
        case True
        have "poly f a=0" by (rule Comp_isRoot_f[OF h hs hr0 True])
        then have "0<rootMultiplicity a f" using structure_multiplicity_pos[OF fnz] by blast
        with bound mult show ?thesis by arith
      next
        case False
        then show ?thesis by (simp add: structure_multiplicity_nonroot)
      qed
    qed
  qed
  obtain q where q: "[:-1,1:]*f = r*q" using dvd by (elim dvdE)
  have qnz: "q\<noteq>0" using q gnz by auto
  have deg1: "degree ([:-1,1:]*f) = 1+degree f"
    using fnz by (simp add: degree_mult_eq del: mult_pCons_left mult_pCons_right)
  have deg2: "degree ([:-1,1:]*f) = degree r+degree q"
    by (simp only: q degree_mult_eq[OF rnz qnz])
  have lt: "degree f<degree r" by (rule Comp_natDegree_f_lt[OF h hs hr hf])
  have "degree q=0" using deg1 deg2 lt by arith
  then obtain c where qc: "q=[:c:]" by (elim degree_eq_zeroE)
  have f0: "poly f 0 = -1" by (rule Comp_f_eval_zero[OF h hr0])
  have "poly ([:-1,1:]*f) 0 = poly (r*q) 0" using q by simp
  then have "c=1" by (simp add: qc hr0 f0)
  with q qc show ?thesis by simp
qed

end
