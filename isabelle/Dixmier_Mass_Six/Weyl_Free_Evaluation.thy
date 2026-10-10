theory Weyl_Free_Evaluation
  imports Free_Word_Algebra "PBW_Finite_Coordinates"
begin

declare id_def [simp del]

lemma free_op_comp_zero_left [simp]: "op_comp 0 T = 0"
  by (rule ext) (simp add: op_comp_def)
lemma free_op_comp_zero_right [simp]: "poly_linear T \<Longrightarrow> op_comp T 0 = 0"
  by (rule ext) (simp add: op_comp_def poly_linear_zero_image)
lemma free_op_scalar_add:
  "op_scalar (a+b) = op_scalar a + op_scalar b"
  by (rule ext) (simp add: op_scalar_def smult_add_left)
lemma free_op_scalar_mult:
  "op_scalar (a*b) = op_comp (op_scalar a) (op_scalar b)"
  by (rule ext) (simp add: op_scalar_def op_comp_def smult_smult)
lemma free_op_scalar_zero [simp]: "op_scalar 0 = 0"
  by (rule ext) (simp add: op_scalar_def)
lemma free_op_scalar_one [simp]: "op_scalar 1 = id"
  by (rule ext) (simp add: op_scalar_def)
lemma free_op_smult_add:
  "(\<lambda>p. smult (a+b) (T p)) = (\<lambda>p. smult a (T p)) + (\<lambda>p. smult b (T p))"
  by (rule ext) (simp add: smult_add_left)

fun word_operator_list :: "bool list \<Rightarrow> 'k::field poly_operator" where
  "word_operator_list [] = id"
| "word_operator_list (b#bs) = op_comp (if b then y_op else x_op) (word_operator_list bs)"

definition word_operator :: "weyl_word \<Rightarrow> 'k::field poly_operator" where
  "word_operator w = (case w of Word bs \<Rightarrow> word_operator_list bs)"

lemma word_operator_list_linear [simp]: "poly_linear (word_operator_list bs)"
  by (induction bs) (auto simp: id_def[symmetric] intro: poly_linear_comp)
lemma word_operator_linear [simp]: "poly_linear (word_operator w)"
  by (cases w) (simp add: word_operator_def)
lemma word_operator_list_append:
  "word_operator_list (u@v) = op_comp (word_operator_list u) (word_operator_list v)"
  by (induction u) (simp_all add: op_comp_def)
lemma word_operator_add:
  "word_operator (u+v) = op_comp (word_operator u) (word_operator v)"
  by (cases u; cases v) (simp add: word_operator_def word_operator_list_append)
lemma word_operator_zero [simp]: "word_operator 0 = id"
  by (simp add: free_word_zero word_operator_def)
lemma word_operator_X [simp]: "word_operator (Word [False]) = x_op"
  by (simp add: word_operator_def)
lemma word_operator_Y [simp]: "word_operator (Word [True]) = y_op"
  by (simp add: word_operator_def)
lemma word_operator_list_in_weyl:
  "word_operator_list bs \<in> (weyl_algebra :: 'k::field poly_operator set)"
proof (induction bs)
  case Nil show ?case by (simp only: word_operator_list.simps weyl_algebra_def op_adjoin_id)
next
  case (Cons b bs)
  have gen: "(if b then y_op else x_op) \<in> (weyl_algebra :: 'k poly_operator set)" by simp
  show ?case unfolding word_operator_list.simps weyl_algebra_def
    by (rule op_adjoin.comp[OF gen[unfolded weyl_algebra_def]
      Cons.IH[unfolded weyl_algebra_def]])
qed
lemma word_operator_in_weyl: "word_operator w \<in> weyl_algebra"
  by (cases w) (simp add: word_operator_def word_operator_list_in_weyl)

definition evaluate_weyl_free :: "'k::field weyl_free \<Rightarrow> 'k poly_operator" where
  "evaluate_weyl_free f = (\<lambda>p. \<Sum>w\<in>Poly_Mapping.keys f.
    smult (Poly_Mapping.lookup f w) (word_operator w p))"

lemma evaluate_weyl_free_zero [simp]: "evaluate_weyl_free 0 = 0"
  by (rule ext) (simp add: evaluate_weyl_free_def)
lemma evaluate_weyl_free_single:
  "evaluate_weyl_free (Poly_Mapping.single w c) = (\<lambda>p. smult c (word_operator w p))"
  by (cases "c=0"; rule ext)
     (simp_all add: evaluate_weyl_free_def Poly_Mapping.keys_single Poly_Mapping.lookup_single)
lemma evaluate_weyl_free_add:
  "evaluate_weyl_free (f+g) = evaluate_weyl_free f + evaluate_weyl_free g"
proof (rule ext)
  fix p
  show "evaluate_weyl_free (f+g) p = (evaluate_weyl_free f + evaluate_weyl_free g) p"
    unfolding evaluate_weyl_free_def plus_fun_def
    by (rule Poly_Mapping.setsum_keys_plus_distrib) (simp_all add: smult_add_left)
qed
lemma evaluate_weyl_free_scalar [simp]: "evaluate_weyl_free (free_scalar c) = op_scalar c"
  by (simp add: free_scalar_def evaluate_weyl_free_single op_scalar_def)
lemma evaluate_weyl_free_one [simp]: "evaluate_weyl_free 1 = id"
  using evaluate_weyl_free_scalar[of 1] by simp
lemma evaluate_weyl_free_X [simp]: "evaluate_weyl_free free_X = x_op"
  by (simp add: free_X_def evaluate_weyl_free_single)
lemma evaluate_weyl_free_Y [simp]: "evaluate_weyl_free free_Y = y_op"
  by (simp add: free_Y_def evaluate_weyl_free_single)

lemma evaluate_weyl_free_linear [simp]: "poly_linear (evaluate_weyl_free f)"
proof (induction f rule: free_induct)
  case zero show ?case by (simp only: evaluate_weyl_free_zero poly_linear_zero)
next
  case (add f g)
  then show ?case unfolding evaluate_weyl_free_add by (blast intro: poly_linear_add)
next
  case (single w c)
  show ?case unfolding evaluate_weyl_free_single
    by (rule poly_linear_smult[OF word_operator_linear])
qed
lemma evaluate_weyl_free_in_weyl: "evaluate_weyl_free f \<in> weyl_algebra"
proof (induction f rule: free_induct)
  case zero show ?case by (simp only: evaluate_weyl_free_zero weyl_algebra_def op_adjoin_zero)
next
  case (add f g)
  then show ?case unfolding evaluate_weyl_free_add weyl_algebra_def by (rule op_adjoin.add)
next
  case (single w c)
  show ?case unfolding evaluate_weyl_free_single weyl_algebra_def
    by (rule op_adjoin_smult) (simp add: word_operator_in_weyl[unfolded weyl_algebra_def])
qed

lemma free_single_evaluation_product:
  "evaluate_weyl_free (Poly_Mapping.single u a * Poly_Mapping.single v b) =
    op_comp (evaluate_weyl_free (Poly_Mapping.single u a))
      (evaluate_weyl_free (Poly_Mapping.single v b))"
  by (rule ext)
     (simp add: Poly_Mapping.mult_single evaluate_weyl_free_single word_operator_add
       op_comp_def poly_linear_def[THEN iffD1, THEN conjunct2, rule_format] smult_smult)

lemma evaluate_weyl_free_mult:
  "evaluate_weyl_free (f*g) = op_comp (evaluate_weyl_free f) (evaluate_weyl_free g)"
proof (induction f rule: free_induct)
  case zero show ?case by (simp only: mult_zero_left evaluate_weyl_free_zero free_op_comp_zero_left)
next
  case (add f h)
  show ?case
    by (rule ext) (use add in \<open>simp add: distrib_right evaluate_weyl_free_add op_comp_def\<close>)
next
  case (single u a)
  show ?case
  proof (induction g rule: free_induct)
    case zero show ?case
      by (simp only: mult_zero_right evaluate_weyl_free_zero
        free_op_comp_zero_right[OF evaluate_weyl_free_linear])
  next
    case (add g h)
    have lin: "evaluate_weyl_free (Poly_Mapping.single u a) (p+q) =
      evaluate_weyl_free (Poly_Mapping.single u a) p +
      evaluate_weyl_free (Poly_Mapping.single u a) q" for p q
      using evaluate_weyl_free_linear[of "Poly_Mapping.single u a"]
      unfolding poly_linear_def by blast
    show ?case
      by (rule ext) (use add in \<open>simp add: distrib_left evaluate_weyl_free_add op_comp_def lin\<close>)
  next
    case (single v b)
    show ?case by (rule free_single_evaluation_product)
  qed
qed

lemma evaluate_weyl_free_minus:
  "evaluate_weyl_free (-f) = - evaluate_weyl_free f"
proof -
  have "evaluate_weyl_free f + evaluate_weyl_free (-f) = 0"
    using evaluate_weyl_free_add[of f "-f"] by simp
  then show ?thesis by (metis add_eq_0_iff)
qed
lemma evaluate_weyl_free_diff:
  "evaluate_weyl_free (f-g) = evaluate_weyl_free f - evaluate_weyl_free g"
  by (simp only: diff_conv_add_uminus evaluate_weyl_free_add evaluate_weyl_free_minus)

text \<open>Actual linear operators use composition in their ring record. No
pointwise function multiplication occurs in the algebra-homomorphism contract.\<close>

definition linear_operator_ring :: "'k::field poly_operator ring" where
  "linear_operator_ring = \<lparr>carrier = {T. poly_linear T}, monoid.mult = op_comp,
    monoid.one = id, ring.zero = 0, ring.add = (+)\<rparr>"

lemma linear_operator_ring_is_ring:
  "ring (linear_operator_ring :: 'k::field poly_operator ring)"
proof (rule ringI)
  show "abelian_group (linear_operator_ring :: 'k poly_operator ring)"
  proof (rule abelian_groupI)
    show "\<And>x y. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
      y \<in> carrier linear_operator_ring \<Longrightarrow>
      ring.add linear_operator_ring x y \<in> carrier linear_operator_ring"
      by (simp add: linear_operator_ring_def poly_linear_add)
    show "ring.zero (linear_operator_ring :: 'k poly_operator ring) \<in> carrier linear_operator_ring"
      by (simp add: linear_operator_ring_def)
    show "\<And>x y z. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
      y \<in> carrier linear_operator_ring \<Longrightarrow> z \<in> carrier linear_operator_ring \<Longrightarrow>
      ring.add linear_operator_ring (ring.add linear_operator_ring x y) z =
      ring.add linear_operator_ring x (ring.add linear_operator_ring y z)"
      by (simp add: linear_operator_ring_def add.assoc)
    show "\<And>x y. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
      y \<in> carrier linear_operator_ring \<Longrightarrow>
      ring.add linear_operator_ring x y = ring.add linear_operator_ring y x"
      by (simp add: linear_operator_ring_def add.commute)
    show "\<And>x. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
      ring.add linear_operator_ring (ring.zero linear_operator_ring) x = x"
      by (simp add: linear_operator_ring_def)
    show "\<And>x. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
      \<exists>y\<in>carrier linear_operator_ring. ring.add linear_operator_ring y x = ring.zero linear_operator_ring"
    proof -
      fix x :: "'k poly_operator"
      assume "x \<in> carrier linear_operator_ring"
      then have lin: "poly_linear x" by (simp add: linear_operator_ring_def)
      have "poly_linear (0-x)" by (rule poly_linear_diff[OF poly_linear_zero lin])
      then show "\<exists>y\<in>carrier linear_operator_ring. ring.add linear_operator_ring y x = ring.zero linear_operator_ring"
        by (intro bexI[of _ "-x"]) (simp_all add: linear_operator_ring_def)
    qed
  qed
  show "Group.monoid (linear_operator_ring :: 'k poly_operator ring)"
    by (rule monoidI) (auto simp: linear_operator_ring_def op_comp_assoc intro: poly_linear_comp)
  show "\<And>x y z. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
    y \<in> carrier linear_operator_ring \<Longrightarrow> z \<in> carrier linear_operator_ring \<Longrightarrow>
    monoid.mult linear_operator_ring (ring.add linear_operator_ring x y) z =
    ring.add linear_operator_ring (monoid.mult linear_operator_ring x z) (monoid.mult linear_operator_ring y z)"
    by (simp add: linear_operator_ring_def op_comp_add_left)
  show "\<And>x y z. x \<in> carrier (linear_operator_ring :: 'k poly_operator ring) \<Longrightarrow>
    y \<in> carrier linear_operator_ring \<Longrightarrow> z \<in> carrier linear_operator_ring \<Longrightarrow>
    monoid.mult linear_operator_ring z (ring.add linear_operator_ring x y) =
    ring.add linear_operator_ring (monoid.mult linear_operator_ring z x) (monoid.mult linear_operator_ring z y)"
    by (simp add: linear_operator_ring_def op_comp_add_right)
qed

lemma evaluate_weyl_free_ring_hom:
  "evaluate_weyl_free \<in> ring_hom (free_ring :: 'k::field weyl_free ring) linear_operator_ring"
  by (rule ring_hom_memI)
     (simp_all add: linear_operator_ring_def evaluate_weyl_free_mult evaluate_weyl_free_add)
lemma evaluate_weyl_free_ring_hom_ring:
  "ring_hom_ring (free_ring :: 'k::field weyl_free ring) linear_operator_ring evaluate_weyl_free"
  by (rule ring_hom_ringI2[OF free_ring_is_ring linear_operator_ring_is_ring evaluate_weyl_free_ring_hom])

lemma evaluate_weyl_free_relation:
  "evaluate_weyl_free (weyl_relation :: 'k::field weyl_free) = 0"
  by (simp add: weyl_relation_def evaluate_weyl_free_diff evaluate_weyl_free_mult yx_commutator)

lemma weyl_relation_ideal_subset_kernel:
  "(weyl_relation_ideal :: 'k::field weyl_free set) \<subseteq>
    a_kernel free_ring linear_operator_ring evaluate_weyl_free"
proof -
  have ki: "ideal (a_kernel (free_ring :: 'k weyl_free ring) linear_operator_ring evaluate_weyl_free) free_ring"
    by (rule ring_hom_ring.kernel_is_ideal[OF evaluate_weyl_free_ring_hom_ring])
  show ?thesis unfolding weyl_relation_ideal_def
    by (rule ring.genideal_minimal[OF free_ring_is_ring ki])
       (simp add: a_kernel_def' linear_operator_ring_def evaluate_weyl_free_relation)
qed

lemma evaluate_weyl_free_zero_on_relation_ideal:
  "f \<in> (weyl_relation_ideal :: 'k::field weyl_free set) \<Longrightarrow> evaluate_weyl_free f = 0"
  using weyl_relation_ideal_subset_kernel[where 'k='k]
  by (auto simp: a_kernel_def' linear_operator_ring_def)

end
