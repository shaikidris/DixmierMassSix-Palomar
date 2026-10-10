theory Finite_Cut_Map_Chain
  imports "Polynomial_Finite_Cut_Image"
    "Joseph_Local_Nilpotence"
begin

lemma finite_cut_aut_diff:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and U: "U\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts (T-U)=ramified_finite_cut_aut l cuts T-ramified_finite_cut_aut l cuts U"
proof (induction cuts)
  case Nil show ?case by simp
next
  case (Cons a cuts)
  have hom: "ramified_alg_hom_on l (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a))"
    using ramified_cut_aut_certificate[OF l, of "cut_rho a" "cut_sigma a" "cut_root a"]
    unfolding ramified_alg_aut_on_def by blast
  have Tc: "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  have Uc: "ramified_finite_cut_aut l cuts U\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l U])
  show ?case by (simp only: ramified_finite_cut_aut.simps Cons.IH ramified_hom_diff[OF hom Tc Uc])
qed

lemma finite_cut_aut_comp:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and U: "U\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts (laurent_comp T U)=
    laurent_comp (ramified_finite_cut_aut l cuts T) (ramified_finite_cut_aut l cuts U)"
proof (induction cuts)
  case Nil show ?case by simp
next
  case (Cons a cuts)
  have hom: "ramified_alg_hom_on l (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a))"
    using ramified_cut_aut_certificate[OF l, of "cut_rho a" "cut_sigma a" "cut_root a"]
    unfolding ramified_alg_aut_on_def by blast
  have Tc: "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  have Uc: "ramified_finite_cut_aut l cuts U\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l U])
  show ?case by (simp only: ramified_finite_cut_aut.simps Cons.IH ramified_hom_comp[OF hom Tc Uc])
qed

lemma finite_cut_aut_zero:
  assumes l: "0<l"
  shows "ramified_finite_cut_aut l cuts (0::laurent_operator)=0"
proof -
  have z: "(0::laurent_operator)\<in>ramified_operator_algebra l"
    unfolding ramified_operator_algebra_def by (rule laurent_adjoin_zero)
  have same: "ramified_finite_cut_aut l cuts (0-0)=
    ramified_finite_cut_aut l cuts 0-ramified_finite_cut_aut l cuts 0"
    by (rule finite_cut_aut_diff[OF l z z])
  show ?thesis using same by (simp only: diff_self)
qed

lemma finite_cut_image_zero:
  assumes l: "0<l"
  shows "finite_cut_image l cuts (0::complex poly_operator)=0"
  by (simp only: finite_cut_image_def polynomial_ramified_lift_zero finite_cut_aut_zero[OF l])

lemma finite_cut_image_commutator:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and R: "R\<in>weyl_algebra"
  shows "finite_cut_image l cuts (op_comp P R-op_comp R P)=
    laurent_comp (finite_cut_image l cuts P) (finite_cut_image l cuts R)-
    laurent_comp (finite_cut_image l cuts R) (finite_cut_image l cuts P)"
proof -
  have Pc: "polynomial_ramified_lift l P\<in>ramified_operator_algebra l"
    and Rc: "polynomial_ramified_lift l R\<in>ramified_operator_algebra l"
    by (rule polynomial_ramified_lift_carrier)+
  have PR: "laurent_comp (polynomial_ramified_lift l P) (polynomial_ramified_lift l R)\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_comp[OF Pc Rc])
  have RP: "laurent_comp (polynomial_ramified_lift l R) (polynomial_ramified_lift l P)\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_comp[OF Rc Pc])
  show ?thesis by (simp only: finite_cut_image_def polynomial_ramified_lift_commutator[OF l R P]
    finite_cut_aut_diff[OF l PR RP] finite_cut_aut_comp[OF l Pc Rc] finite_cut_aut_comp[OF l Rc Pc])
qed

primrec ramifiedJosephChain :: "laurent_operator \<Rightarrow> laurent_operator \<Rightarrow> nat \<Rightarrow> laurent_operator" where
  "ramifiedJosephChain U V 0=V"
| "ramifiedJosephChain U V (Suc n)=laurent_comp U (ramifiedJosephChain U V n)-laurent_comp (ramifiedJosephChain U V n) U"

lemma finite_cut_image_joseph_chain:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and R: "R\<in>weyl_algebra"
  shows "finite_cut_image l cuts (josephCommutatorChain P R n)=
    ramifiedJosephChain (finite_cut_image l cuts P) (finite_cut_image l cuts R) n"
proof (induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  have carrier: "josephCommutatorChain P R n\<in>weyl_algebra"
    by (rule josephCommutatorChain_weyl[OF P R])
  show ?case by (simp only: josephCommutatorChain.simps finite_cut_image_commutator[OF l P carrier]
    Suc.IH ramifiedJosephChain.simps)
qed

lemma ramified_generated_chain_terminates_of_finite_cut_map:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and R: "R\<in>op_adjoin {P,Q}"
  shows "\<exists>n. ramifiedJosephChain (finite_cut_image l cuts P) (finite_cut_image l cuts R) n=0"
proof -
  have Rc: "R\<in>weyl_algebra" using weyl_nested_adjoin[of "{P,Q}"] P Q R by blast
  obtain n where killed: "josephCommutatorChain P R n=0"
    using joseph_chain_terminates_on_adjoin[OF P Q exact R] by blast
  have mapped: "ramifiedJosephChain (finite_cut_image l cuts P) (finite_cut_image l cuts R) n=0"
    using finite_cut_image_joseph_chain[OF l P Rc, where cuts=cuts and n=n]
    by (simp only: killed finite_cut_image_zero[OF l])
  show ?thesis
  proof (rule exI[of _ n])
    show "ramifiedJosephChain (finite_cut_image l cuts P) (finite_cut_image l cuts R) n=0"
      by (rule mapped)
  qed
qed

end
