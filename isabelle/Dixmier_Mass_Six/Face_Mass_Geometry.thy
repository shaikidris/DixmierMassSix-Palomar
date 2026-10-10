theory Face_Mass_Geometry
  imports "Weyl_Leading_Forms"
begin

definition weighted_homogeneous :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a::field bivariate \<Rightarrow> bool" where
  "weighted_homogeneous rho sigma m F \<longleftrightarrow> (\<forall>u\<in>biv_support F. pair_weight rho sigma u=m)"
lemma weighted_component_homogeneous:
  "weighted_homogeneous rho sigma m (weighted_component rho sigma m F)"
  by (auto simp: weighted_homogeneous_def weighted_component_support)
lemma weighted_component_support_subset:
  "biv_support (weighted_component rho sigma m (F::complex bivariate)) \<subseteq> biv_support F"
  by (simp only: weighted_component_support) auto
lemma face_grade_support_subset:
  assumes "T\<in>(weyl_algebra::complex poly_operator set)"
  shows "pair_grade ` biv_support (leading_form rho sigma T) \<subseteq> pair_grade ` biv_support (pbw_symbol T)"
  unfolding leading_form_def by (rule image_mono, rule weighted_component_support_subset)
lemma grade_injective_on_homogeneous_face:
  fixes F::"complex bivariate"
  assumes pos: "0<rho+sigma" and hom: "weighted_homogeneous rho sigma m F"
  shows "inj_on pair_grade (biv_support F)"
proof (rule inj_onI)
  fix p q assume p: "p\<in>biv_support F" and q: "q\<in>biv_support F"
    and grade: "pair_grade p=pair_grade q"
  have pw: "pair_weight rho sigma p=m" and qw: "pair_weight rho sigma q=m"
    using hom p q by (auto simp: weighted_homogeneous_def)
  have xi: "int (fst p)=int (fst q)+int (snd p)-int (snd q)"
    using grade by (simp only: pair_grade_def; arith)
  have expansion: "(rho+sigma)*(int (snd p)-int (snd q))=
      pair_weight rho sigma p-pair_weight rho sigma q"
    by (simp add: pair_weight_def xi algebra_simps)
  have prod: "(rho+sigma)*(int (snd p)-int (snd q))=0"
    using expansion pw qw by simp
  have nz: "rho+sigma\<noteq>0" using pos by arith
  have dy: "int (snd p)-int (snd q)=0" using prod nz by simp
  have sy: "snd p=snd q" using dy by simp
  have sx: "fst p=fst q" using grade sy by (simp add: pair_grade_def)
  show "p=q" using sx sy by (simp add: prod_eq_iff)
qed
lemma face_term_count_le_mass:
  assumes T: "T\<in>(weyl_algebra::complex poly_operator set)" and pos: "0<rho+sigma"
  shows "card (biv_support (leading_form rho sigma T))\<le>weyl_mass T"
proof -
  have hom: "weighted_homogeneous rho sigma (v_degree rho sigma T) (leading_form rho sigma T)"
    unfolding leading_form_def by (rule weighted_component_homogeneous)
  have inj: "inj_on pair_grade (biv_support (leading_form rho sigma T))"
    by (rule grade_injective_on_homogeneous_face[OF pos hom])
  have ce: "card (pair_grade ` biv_support (leading_form rho sigma T))=card (biv_support (leading_form rho sigma T))"
    by (rule card_image[OF inj])
  have bound: "card (pair_grade ` biv_support (leading_form rho sigma T))\<le>card (pair_grade ` biv_support (pbw_symbol T))"
    by (rule card_mono) (simp, rule face_grade_support_subset[OF T])
  show ?thesis using bound by (simp only: ce weyl_mass_def)
qed
lemma zero_weight_sum_grade_collision_control:
  "pair_weight 1 (-1) (0,0)=pair_weight 1 (-1) (1,1) \<and>
    pair_grade (0,0)=pair_grade (1,1) \<and> (0::nat,0::nat)\<noteq>(1,1)"
  by (simp add: pair_weight_def pair_grade_def)
lemma negative_coordinate_same_face_control:
  "pair_weight 2 (-1) (1,1)=pair_weight 2 (-1) (2,3) \<and>
    pair_grade (1,1)\<noteq>pair_grade (2,3)"
  by (simp add: pair_weight_def pair_grade_def)
lemma zero_face_mass_control:
  "card (biv_support (leading_form rho sigma (0::complex poly_operator)))=weyl_mass (0::complex poly_operator)"
  by (simp add: leading_form_def weyl_mass_def)
end
