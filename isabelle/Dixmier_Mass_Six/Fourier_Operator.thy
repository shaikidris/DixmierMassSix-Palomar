theory Fourier_Operator
  imports "PBW_Finite_Coordinates" "HOL-Library.Poly_Mapping"
begin

declare id_def [simp del]

definition fourier_summand :: "'a::field poly_operator \<Rightarrow> nat\<times>nat \<Rightarrow> 'a poly_operator" where
  "fourier_summand T u = (\<lambda>p. smult (pbw_coeff T (fst u) (snd u))
    (smult ((-1)^(snd u)) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p)))"

definition fourier_summand_support :: "'a::field poly_operator \<Rightarrow> (nat\<times>nat) set" where
  "fourier_summand_support T = {u. fourier_summand T u \<noteq> 0}"

definition fourier_op :: "'a::field poly_operator \<Rightarrow> 'a poly_operator" where
  "fourier_op T = (if finite (fourier_summand_support T)
    then (\<Sum>u\<in>fourier_summand_support T. fourier_summand T u) else 0)"

lemma fourier_infinite_support:
  "\<not> finite (fourier_summand_support T) \<Longrightarrow> fourier_op T=0"
  by (simp add: fourier_op_def)

lemma fourier_actual_support_sum:
  "fourier_op T = (\<Sum>u\<in>fourier_summand_support T. fourier_summand T u)"
  by (cases "finite (fourier_summand_support T)") (simp_all add: fourier_op_def)

lemma fourier_weyl_power:
  "T\<in>weyl_algebra \<Longrightarrow> (T ^^ n)\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_power; assumption)
lemma fourier_weyl_comp:
  "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> op_comp T U\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.comp; assumption)
lemma fourier_weyl_scale:
  "T\<in>weyl_algebra \<Longrightarrow> (\<lambda>p. smult c (T p))\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_smult; assumption)
lemma fourier_weyl_sum:
  "(\<And>u. u\<in>S \<Longrightarrow> f u\<in>weyl_algebra) \<Longrightarrow> (\<Sum>u\<in>S. f u)\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_sum; assumption)

lemma fourier_summand_in_weyl:
  "fourier_summand T u\<in>(weyl_algebra :: 'a::field poly_operator set)"
  unfolding fourier_summand_def
  by (intro fourier_weyl_scale fourier_weyl_comp fourier_weyl_power) simp_all

lemma fourier_all_operators_in_weyl:
  "fourier_op T\<in>(weyl_algebra :: 'a::field poly_operator set)"
  unfolding fourier_actual_support_sum
  by (rule fourier_weyl_sum) (rule fourier_summand_in_weyl)

lemma fourier_all_operators_linear:
  "poly_linear (fourier_op T)"
  by (rule weyl_linear[OF fourier_all_operators_in_weyl])

lemma fourier_mem_A1:
  fixes T :: "'a::field_char_0 poly_operator"
  assumes "T\<in>weyl_algebra"
  shows "fourier_op T\<in>weyl_algebra"
  by (rule fourier_all_operators_in_weyl)

lemma fourier_eq_finitePBWSum:
  fixes T :: "'a::field_char_0 poly_operator" and c :: "(nat\<times>nat,'a) poly_mapping"
  assumes hT: "T\<in>weyl_algebra"
    and hc: "finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c)=T"
  shows "fourier_op T = (\<Sum>u\<in>Poly_Mapping.keys c. (\<lambda>p.
    smult (Poly_Mapping.lookup c u)
      (smult ((-1)^(snd u)) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p))))"
proof -
  have coeff: "pbw_coeff T (fst u) (snd u)=Poly_Mapping.lookup c u" for u
    by (simp add: hc[symmetric] pbw_coeff_finite_normal_sum Poly_Mapping.in_keys_iff)
  have sub: "fourier_summand_support T \<subseteq> Poly_Mapping.keys c"
    by (auto simp: fourier_summand_support_def fourier_summand_def coeff Poly_Mapping.in_keys_iff)
  have sums: "(\<Sum>u\<in>Poly_Mapping.keys c. fourier_summand T u) =
    (\<Sum>u\<in>fourier_summand_support T. fourier_summand T u)"
    by (rule sum.mono_neutral_right[OF Poly_Mapping.finite_keys sub])
      (auto simp: fourier_summand_support_def)
  have "fourier_op T = (\<Sum>u\<in>Poly_Mapping.keys c. fourier_summand T u)"
    by (simp only: fourier_actual_support_sum sums)
  also have "... = (\<Sum>u\<in>Poly_Mapping.keys c. (\<lambda>p.
    smult (Poly_Mapping.lookup c u)
      (smult ((-1)^(snd u)) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p))))"
    by (rule sum.cong) (simp_all only: fourier_summand_def coeff)
  finally show ?thesis .
qed

lemma fourier_zero [simp]: "fourier_op (0::'a::field poly_operator)=0"
proof -
  have summand_zero: "fourier_summand (0::'a poly_operator) u=0" for u
    by (rule ext) (simp add: fourier_summand_def pbw_coeff_def)
  show ?thesis by (simp add: fourier_op_def fourier_summand_support_def summand_zero)
qed

lemma fourier_normal_monomial:
  "fourier_op (normal_monomial i j :: 'a::field_char_0 poly_operator) =
    (\<lambda>p. smult ((-1)^j) (op_comp (y_op ^^ i) (x_op ^^ j) p))"
proof -
  let ?c = "Poly_Mapping.single (i,j) (1::'a)"
  have rep: "finite_normal_sum (Poly_Mapping.keys ?c) (Poly_Mapping.lookup ?c) = normal_monomial i j"
    by (rule ext) (simp add: finite_normal_sum_def Poly_Mapping.lookup_single when_def)
  note h = fourier_eq_finitePBWSum[OF normal_monomial_in_weyl rep]
  show ?thesis using h by (simp add: Poly_Mapping.lookup_single when_def)
qed

end
