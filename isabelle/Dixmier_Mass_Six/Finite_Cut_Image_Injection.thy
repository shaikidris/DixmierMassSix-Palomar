theory Finite_Cut_Image_Injection
  imports Finite_Cut_Map_Chain
begin

lemma ramified_cut_aut_injective_on_carrier:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and U: "U\<in>ramified_operator_algebra l"
    and equal: "ramified_cut_aut l rho sigma c T=ramified_cut_aut l rho sigma c U"
  shows "T=U"
proof -
  let ?G = "ramified_shear_hom l (-ramified_cut_shift l rho sigma c)"
  have certificate: "ramified_alg_aut_on l (ramified_cut_aut l rho sigma c) ?G"
    by (rule ramified_cut_aut_certificate[OF l])
  have left: "?G (ramified_cut_aut l rho sigma c T)=T"
    and right: "?G (ramified_cut_aut l rho sigma c U)=U"
    using certificate T U unfolding ramified_alg_aut_on_def by blast+
  have image: "?G (ramified_cut_aut l rho sigma c T)=?G (ramified_cut_aut l rho sigma c U)"
    by (rule arg_cong[OF equal])
  show ?thesis using image by (simp only: left right)
qed

lemma finite_cut_aut_injective_on_carrier:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and U: "U\<in>ramified_operator_algebra l"
    and equal: "ramified_finite_cut_aut l cuts T=ramified_finite_cut_aut l cuts U"
  shows "T=U"
  using equal
proof (induction cuts)
  case Nil
  show ?case using Nil.prems by (simp only: ramified_finite_cut_aut.simps)
next
  case (Cons a cuts)
  have Tc: "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  have Uc: "ramified_finite_cut_aut l cuts U\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l U])
  have equal_step: "ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a)
       (ramified_finite_cut_aut l cuts T)=
    ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a)
       (ramified_finite_cut_aut l cuts U)"
    using Cons.prems by (simp only: ramified_finite_cut_aut.simps)
  have equal_tail: "ramified_finite_cut_aut l cuts T=ramified_finite_cut_aut l cuts U"
    by (rule ramified_cut_aut_injective_on_carrier[OF l Tc Uc equal_step])
  show ?case by (rule Cons.IH[OF equal_tail])
qed

lemma finite_cut_image_injective:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and Q: "Q\<in>weyl_algebra"
    and equal: "finite_cut_image l cuts P=finite_cut_image l cuts Q"
  shows "P=Q"
proof -
  have lifted: "polynomial_ramified_lift l P=polynomial_ramified_lift l Q"
    by (rule finite_cut_aut_injective_on_carrier[OF l polynomial_ramified_lift_carrier
      polynomial_ramified_lift_carrier]) (use equal in \<open>simp only: finite_cut_image_def\<close>)
  show ?thesis by (rule polynomial_ramified_lift_injective[OF l P Q lifted])
qed

lemma finite_cut_image_nonzero_iff:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "finite_cut_image l cuts P\<noteq>0 \<longleftrightarrow> P\<noteq>0"
proof -
  have z: "(0::complex poly_operator)\<in>weyl_algebra"
    unfolding weyl_algebra_def by (rule op_adjoin_zero)
  have forward: "finite_cut_image l cuts P=0 \<Longrightarrow> P=0"
  proof -
    assume image: "finite_cut_image l cuts P=0"
    have equal: "finite_cut_image l cuts P=finite_cut_image l cuts 0"
      by (simp only: image finite_cut_image_zero[OF l])
    show "P=0" by (rule finite_cut_image_injective[OF l P z equal])
  qed
  have backward: "P=0 \<Longrightarrow> finite_cut_image l cuts P=0"
    by (simp only: finite_cut_image_zero[OF l])
  show ?thesis using forward backward by blast
qed

end
