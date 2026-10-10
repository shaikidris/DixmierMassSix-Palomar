theory Abstract_Faithfulness
  imports Abstract_Finite_Coordinates
begin

text \<open>The concrete carrier ring and forward homomorphism need only a
field. Characteristic zero begins below, at prescribed PBW recovery.\<close>

definition weyl_operator_ring :: "'k::field poly_operator ring" where
  "weyl_operator_ring = linear_operator_ring \<lparr>carrier := weyl_algebra\<rparr>"

lemma weyl_operator_ring_simps [simp]:
  "carrier weyl_operator_ring = weyl_algebra"
  "monoid.mult weyl_operator_ring = op_comp"
  "monoid.one weyl_operator_ring = id"
  "ring.zero weyl_operator_ring = 0"
  "ring.add weyl_operator_ring = (+)"
  by (simp_all add: weyl_operator_ring_def linear_operator_ring_def)

lemma weyl_operator_ring_is_ring:
  "ring (weyl_operator_ring :: 'k::field poly_operator ring)"
proof -
  interpret E: ring_hom_ring "(abstract_weyl_ring :: 'k weyl_free set ring)"
    linear_operator_ring abstract_to_concrete
    by (rule ring_hom_ringI2[OF abstract_weyl_ring_is_ring linear_operator_ring_is_ring
      abstract_to_concrete_ring_hom])
  show ?thesis using E.img_is_ring
    by (simp only: abstract_to_concrete_image weyl_operator_ring_def)
qed

lemma abstract_to_concrete_weyl_ring_hom:
  "abstract_to_concrete \<in> ring_hom (abstract_weyl_ring :: 'k::field weyl_free set ring)
    weyl_operator_ring"
  using abstract_to_concrete_ring_hom[where 'k='k] abstract_to_concrete_in_weyl[where 'k='k]
  by (auto simp add: ring_hom_def weyl_operator_ring_def)

context
  fixes K :: "'k::field_char_0 itself"
begin

interpretation A: abstract_normal_arithmetic K .
abbreviation Q :: "'k weyl_free set ring" where "Q \<equiv> abstract_weyl_ring"

lemma abstract_to_concrete_zero_imp_zero:
  assumes z: "z \<in> carrier Q" and hz: "abstract_to_concrete z = 0"
  shows "z = ring.zero Q"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "abstract_normal_ordered_sum c = z"
    using A.abstract_exists_finite_coordinates[OF z] by blast
  have image: "finite_normal_sum {u. c u \<noteq> 0} c = (0 :: 'k poly_operator)"
    using A.abstract_evaluation_normal_ordered_sum[OF fin] rep hz by metis
  have fin0: "finite {u :: nat \<times> nat. (0 :: 'k) \<noteq> 0}" by simp
  have coeff0: "c = (\<lambda>_. 0)"
    by (rule finite_coordinates_unique[OF fin fin0])
       (simp only: finite_normal_sum_zero image)
  show ?thesis using rep
    by (simp only: coeff0 abstract_normal_ordered_sum_def A.abstract_normal_sum_zero)
qed

lemma abstract_to_concrete_injective:
  "inj_on abstract_to_concrete (carrier Q)"
proof (rule inj_onI)
  fix z w
  assume z: "z \<in> carrier Q" and w: "w \<in> carrier Q"
    and eq: "abstract_to_concrete z = abstract_to_concrete w"
  obtain c where cfin: "finite {u. c u \<noteq> 0}" and cz: "abstract_normal_ordered_sum c = z"
    using A.abstract_exists_finite_coordinates[OF z] by blast
  obtain d where dfin: "finite {u. d u \<noteq> 0}" and dw: "abstract_normal_ordered_sum d = w"
    using A.abstract_exists_finite_coordinates[OF w] by blast
  have image_eq: "finite_normal_sum {u. c u \<noteq> 0} c =
    (finite_normal_sum {u. d u \<noteq> 0} d :: 'k poly_operator)"
    using A.abstract_evaluation_normal_ordered_sum[OF cfin]
      A.abstract_evaluation_normal_ordered_sum[OF dfin] cz dw eq by metis
  have "c = d" by (rule finite_coordinates_unique[OF cfin dfin image_eq])
  then show "z = w" using cz dw by simp
qed

lemma abstract_to_concrete_bijective:
  "bij_betw abstract_to_concrete (carrier Q) (weyl_algebra :: 'k poly_operator set)"
  unfolding bij_betw_def
  by (rule conjI[OF abstract_to_concrete_injective abstract_to_concrete_image])

lemma abstract_to_concrete_ring_iso:
  "abstract_to_concrete \<in> ring_iso Q (weyl_operator_ring :: 'k poly_operator ring)"
  by (simp only: ring_iso_def mem_Collect_eq weyl_operator_ring_simps
    abstract_to_concrete_weyl_ring_hom abstract_to_concrete_bijective simp_thms)

end

definition concrete_to_abstract :: "'k::field_char_0 poly_operator \<Rightarrow> 'k weyl_free set" where
  "concrete_to_abstract = inv_into (carrier abstract_weyl_ring) abstract_to_concrete"

lemma concrete_to_abstract_closed:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "concrete_to_abstract T \<in> carrier abstract_weyl_ring"
  unfolding concrete_to_abstract_def
  by (rule inv_into_into) (simp only: abstract_to_concrete_image assms)

lemma concrete_to_abstract_inverse:
  assumes "z \<in> carrier (abstract_weyl_ring :: 'k::field_char_0 weyl_free set ring)"
  shows "concrete_to_abstract (abstract_to_concrete z) = z"
  unfolding concrete_to_abstract_def
  by (rule inv_into_f_f[OF abstract_to_concrete_injective assms])

lemma abstract_to_concrete_inverse:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "abstract_to_concrete (concrete_to_abstract T) = T"
  unfolding concrete_to_abstract_def
  by (rule f_inv_into_f) (simp only: abstract_to_concrete_image assms)

lemma concrete_to_abstract_ring_iso:
  "concrete_to_abstract \<in> ring_iso (weyl_operator_ring :: 'k::field_char_0 poly_operator ring)
    abstract_weyl_ring"
  unfolding concrete_to_abstract_def
  by (rule ring_iso_set_sym[OF abstract_weyl_ring_is_ring abstract_to_concrete_ring_iso])
lemma concrete_to_abstract_ring_hom:
  "concrete_to_abstract \<in> ring_hom (weyl_operator_ring :: 'k::field_char_0 poly_operator ring)
    abstract_weyl_ring"
  using concrete_to_abstract_ring_iso[where 'k='k] by (auto simp only: ring_iso_def mem_Collect_eq)

lemma concrete_to_abstract_X:
  "concrete_to_abstract x_op = (abstract_X :: 'k::field_char_0 weyl_free set)"
  using concrete_to_abstract_inverse[OF quotient_X_closed, where 'k='k]
  by (simp only: abstract_to_concrete_X)
lemma concrete_to_abstract_Y:
  "concrete_to_abstract y_op = (abstract_Y :: 'k::field_char_0 weyl_free set)"
  using concrete_to_abstract_inverse[OF quotient_Y_closed, where 'k='k]
  by (simp only: abstract_to_concrete_Y)
lemma concrete_to_abstract_scalar:
  "concrete_to_abstract (op_scalar c) = (abstract_scalar c :: 'k::field_char_0 weyl_free set)"
  using concrete_to_abstract_inverse[OF quotient_scalar_closed, of c]
  by (simp only: abstract_to_concrete_scalar)
lemma concrete_to_abstract_normal_monomial:
  "concrete_to_abstract (normal_monomial i j) =
    (abstract_normal_monomial i j :: 'k::field_char_0 weyl_free set)"
  using concrete_to_abstract_inverse[OF abstract_normal_arithmetic.abstract_normal_monomial_closed,
    where 'k='k, of i j]
  by (simp only: abstract_normal_arithmetic.abstract_evaluation_normal_monomial)
lemma concrete_to_abstract_normal_ordered_sum:
  assumes "finite {u. c u \<noteq> 0}"
  shows "concrete_to_abstract (finite_normal_sum {u. c u \<noteq> 0} c) =
    (abstract_normal_ordered_sum c :: 'k::field_char_0 weyl_free set)"
proof -
  have closed: "abstract_normal_ordered_sum c \<in> carrier abstract_weyl_ring"
    unfolding abstract_normal_ordered_sum_def
    by (rule abstract_normal_arithmetic.abstract_normal_sum_closed)
  show ?thesis using concrete_to_abstract_inverse[OF closed]
    by (simp only: abstract_normal_arithmetic.abstract_evaluation_normal_ordered_sum[OF assms])
qed

end
