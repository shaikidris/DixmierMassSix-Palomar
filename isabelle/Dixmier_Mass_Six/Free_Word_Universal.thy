theory Free_Word_Universal
  imports Central_Scalar_Ring
begin

text \<open>Ordered evaluation in a carrier-based, possibly noncommutative target.
False is X and True is Y. No nontriviality or injectivity assumption is used.\<close>

fun universal_word_list :: "('a,'r) ring_scheme \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> bool list \<Rightarrow> 'a" where
  "universal_word_list R g [] = monoid.one R"
| "universal_word_list R g (b#bs) = monoid.mult R (g b) (universal_word_list R g bs)"

definition universal_word :: "('a,'r) ring_scheme \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> weyl_word \<Rightarrow> 'a" where
  "universal_word R g w = (case w of Word bs \<Rightarrow> universal_word_list R g bs)"

definition universal_free_eval :: "('a,'r) ring_scheme \<Rightarrow> ('k::field \<Rightarrow> 'a) \<Rightarrow>
    (bool \<Rightarrow> 'a) \<Rightarrow> 'k weyl_free \<Rightarrow> 'a" where
  "universal_free_eval R s g f = central_lcomb R s (universal_word R g)
    (Poly_Mapping.keys f) (Poly_Mapping.lookup f)"

locale free_word_evaluation = central_scalar_ring R s
  for R :: "('a,'r) ring_scheme" and s :: "'k::field \<Rightarrow> 'a" +
  fixes g :: "bool \<Rightarrow> 'a"
  assumes generators_closed: "\<And>b. g b \<in> carrier R"
begin

lemma word_list_closed: "universal_word_list R g bs \<in> carrier R"
proof (induction bs)
  case Nil
  show ?case unfolding universal_word_list.simps by (rule scalar.S.one_closed)
next
  case (Cons b bs)
  show ?case unfolding universal_word_list.simps
    by (rule scalar.S.m_closed[OF generators_closed Cons.IH])
qed

lemma word_closed: "universal_word R g w \<in> carrier R"
  by (cases w) (simp only: universal_word_def weyl_word.case word_list_closed)

lemma word_basis_closed: "universal_word R g \<in> S \<rightarrow> carrier R"
  by (auto simp only: Pi_def intro: word_closed)

lemma word_list_append:
  "universal_word_list R g (us@vs) =
    monoid.mult R (universal_word_list R g us) (universal_word_list R g vs)"
proof (induction us)
  case Nil
  show ?case by (simp only: append_Nil universal_word_list.simps scalar.S.l_one[OF word_list_closed])
next
  case (Cons b bs)
  show ?case
    by (simp only: append_Cons universal_word_list.simps Cons.IH
      scalar.S.m_assoc[OF generators_closed word_list_closed word_list_closed])
qed

lemma word_add:
  "universal_word R g (u+v) = monoid.mult R (universal_word R g u) (universal_word R g v)"
  by (cases u; cases v) (simp only: free_word_add universal_word_def weyl_word.case word_list_append)

lemma word_zero: "universal_word R g 0 = monoid.one R"
  by (simp only: free_word_zero universal_word_def weyl_word.case universal_word_list.simps)

lemma word_generator: "universal_word R g (Word [b]) = g b"
  by (simp only: universal_word_def weyl_word.case universal_word_list.simps scalar.S.r_one[OF generators_closed])

lemma free_eval_closed: "universal_free_eval R s g f \<in> carrier R"
  unfolding universal_free_eval_def by (rule lcomb_closed[OF word_basis_closed])

lemma free_eval_zero: "universal_free_eval R s g 0 = ring.zero R"
  by (simp only: universal_free_eval_def Poly_Mapping.keys_zero lcomb_empty)

lemma free_eval_on:
  assumes fin: "finite S" and sub: "Poly_Mapping.keys f \<subseteq> S"
  shows "universal_free_eval R s g f = central_lcomb R s (universal_word R g) S (Poly_Mapping.lookup f)"
  unfolding universal_free_eval_def
proof (rule lcomb_extend[OF fin sub word_basis_closed])
  fix u assume "u \<in> S - Poly_Mapping.keys f"
  then show "Poly_Mapping.lookup f u = 0"
    by (simp add: Poly_Mapping.not_in_keys_iff_lookup_eq_zero[symmetric])
qed

lemma free_eval_single:
  "universal_free_eval R s g (Poly_Mapping.single w c) = monoid.mult R (s c) (universal_word R g w)"
proof -
  have sub: "Poly_Mapping.keys (Poly_Mapping.single w c) \<subseteq> {w}"
    by (simp only: Poly_Mapping.keys_single; split if_splits; simp)
  have fin: "finite {w}" by simp
  have "universal_free_eval R s g (Poly_Mapping.single w c) =
    central_lcomb R s (universal_word R g) {w} (Poly_Mapping.lookup (Poly_Mapping.single w c))"
    by (rule free_eval_on[OF fin sub])
  also have "... = central_lcomb R s (universal_word R g) {w} (\<lambda>v. if v=w then c else 0)"
    by (rule lcomb_cong[OF word_basis_closed])
       (simp only: Poly_Mapping.lookup_single when_def eq_commute)
  also have "... = monoid.mult R (s c) (universal_word R g w)"
    by (rule lcomb_single[OF singletonI fin word_basis_closed])
  finally show ?thesis .
qed

lemma free_eval_add:
  "universal_free_eval R s g (f+h) =
    ring.add R (universal_free_eval R s g f) (universal_free_eval R s g h)"
proof -
  let ?S = "Poly_Mapping.keys f \<union> Poly_Mapping.keys h"
  have fin: "finite ?S" by simp
  have f: "universal_free_eval R s g f = central_lcomb R s (universal_word R g) ?S (Poly_Mapping.lookup f)"
    by (rule free_eval_on[OF fin]) (rule Un_upper1)
  have h: "universal_free_eval R s g h = central_lcomb R s (universal_word R g) ?S (Poly_Mapping.lookup h)"
    by (rule free_eval_on[OF fin]) (rule Un_upper2)
  have "universal_free_eval R s g (f+h) =
    central_lcomb R s (universal_word R g) ?S (\<lambda>w. Poly_Mapping.lookup f w + Poly_Mapping.lookup h w)"
    by (subst free_eval_on[OF fin Poly_Mapping.keys_add];
        rule lcomb_cong[OF word_basis_closed]; rule Poly_Mapping.lookup_add)
  also have "... = ring.add R (universal_free_eval R s g f) (universal_free_eval R s g h)"
    by (simp only: lcomb_add[OF word_basis_closed] f h)
  finally show ?thesis .
qed

lemma central_product:
  assumes u: "u \<in> carrier R" and v: "v \<in> carrier R"
  shows "monoid.mult R (monoid.mult R (s a) u) (monoid.mult R (s b) v) =
    monoid.mult R (s (a*b)) (monoid.mult R u v)"
proof -
  have middle: "monoid.mult R u (monoid.mult R (s b) v) =
    monoid.mult R (s b) (monoid.mult R u v)"
  proof -
    have "monoid.mult R u (monoid.mult R (s b) v) = monoid.mult R (monoid.mult R u (s b)) v"
      by (rule scalar.S.m_assoc[OF u scalar_closed v, symmetric])
    also have "... = monoid.mult R (monoid.mult R (s b) u) v"
      by (simp only: scalar_central[OF u])
    also have "... = monoid.mult R (s b) (monoid.mult R u v)"
      by (rule scalar.S.m_assoc[OF scalar_closed u v])
    finally show ?thesis .
  qed
  have "monoid.mult R (monoid.mult R (s a) u) (monoid.mult R (s b) v) =
    monoid.mult R (s a) (monoid.mult R u (monoid.mult R (s b) v))"
    by (rule scalar.S.m_assoc[OF scalar_closed u scalar.S.m_closed[OF scalar_closed v]])
  also have "... = monoid.mult R (s a) (monoid.mult R (s b) (monoid.mult R u v))"
    by (simp only: middle)
  also have "... = monoid.mult R (s (a*b)) (monoid.mult R u v)"
    by (simp only: scalar_mult;
        rule scalar.S.m_assoc[OF scalar_closed scalar_closed scalar.S.m_closed[OF u v], symmetric])
  finally show ?thesis .
qed

lemma free_eval_single_product:
  "universal_free_eval R s g (Poly_Mapping.single u a * Poly_Mapping.single v b) =
    monoid.mult R (universal_free_eval R s g (Poly_Mapping.single u a))
      (universal_free_eval R s g (Poly_Mapping.single v b))"
  by (simp only: Poly_Mapping.mult_single free_eval_single word_add
      central_product[OF word_closed word_closed])

lemma free_eval_mult:
  "universal_free_eval R s g (f*h) = monoid.mult R (universal_free_eval R s g f) (universal_free_eval R s g h)"
proof (induction f rule: free_induct)
  case zero
  show ?case by (simp only: mult_zero_left free_eval_zero scalar.S.l_null[OF free_eval_closed])
next
  case (add f k)
  show ?case
    by (simp only: distrib_right free_eval_add add.IH
      scalar.S.l_distr[OF free_eval_closed free_eval_closed free_eval_closed])
next
  case (single u a)
  show ?case
  proof (induction h rule: free_induct)
    case zero
    show ?case by (simp only: mult_zero_right free_eval_zero scalar.S.r_null[OF free_eval_closed])
  next
    case (add h k)
    show ?case
      by (simp only: distrib_left free_eval_add add.IH
        scalar.S.r_distr[OF free_eval_closed free_eval_closed free_eval_closed])
  next
    case (single v b)
    show ?case by (rule free_eval_single_product)
  qed
qed

lemma free_eval_scalar: "universal_free_eval R s g (free_scalar c) = s c"
  by (simp only: free_scalar_def free_eval_single word_zero scalar.S.r_one[OF scalar_closed])

lemma free_eval_one: "universal_free_eval R s g 1 = monoid.one R"
  using free_eval_scalar[of 1] by (simp only: free_scalar_one scalar_one)

lemma free_eval_X: "universal_free_eval R s g free_X = g False"
  by (simp only: free_X_def free_eval_single word_generator scalar_one scalar.S.l_one[OF generators_closed])

lemma free_eval_Y: "universal_free_eval R s g free_Y = g True"
  by (simp only: free_Y_def free_eval_single word_generator scalar_one scalar.S.l_one[OF generators_closed])

lemma free_eval_ring_hom:
  "universal_free_eval R s g \<in> ring_hom (free_ring :: 'k weyl_free ring) R"
  by (rule ring_hom_memI)
     (simp_all only: free_ring_simps free_eval_closed free_eval_mult free_eval_add free_eval_one)

lemma free_eval_ring_hom_ring:
  "ring_hom_ring (free_ring :: 'k weyl_free ring) R (universal_free_eval R s g)"
  by (rule ring_hom_ringI2[OF free_ring_is_ring scalar.S.ring_axioms free_eval_ring_hom])

lemma free_eval_unique:
  assumes hom: "h \<in> ring_hom (free_ring :: 'k weyl_free ring) R"
    and scalars: "\<And>c. h (free_scalar c) = s c"
    and X: "h free_X = g False" and Y: "h free_Y = g True"
  shows "h = universal_free_eval R s g"
proof -
  interpret H: ring_hom_ring "(free_ring :: 'k weyl_free ring)" R h
    by (rule ring_hom_ringI2[OF free_ring_is_ring scalar.S.ring_axioms hom])
  have hzero: "h 0 = ring.zero R" using H.hom_zero by (simp only: free_ring_simps)
  have hone: "h 1 = monoid.one R" using H.hom_one by (simp only: free_ring_simps)
  have hadd: "h (a+b) = ring.add R (h a) (h b)" for a b
    using H.hom_add[of a b] by (simp only: free_ring_simps UNIV_I)
  have hmult: "h (a*b) = monoid.mult R (h a) (h b)" for a b
    using H.hom_mult[of a b] by (simp only: free_ring_simps UNIV_I)
  have hgen: "h (Poly_Mapping.single (Word [b]) 1) = g b" for b
    using X Y by (cases b) (simp_all only: free_X_def free_Y_def)
  have hword: "h (Poly_Mapping.single (Word bs) 1) = universal_word_list R g bs" for bs
  proof (induction bs)
    case Nil
    show ?case by (simp only: free_word_zero[symmetric] Poly_Mapping.single_one hone universal_word_list.simps)
  next
    case (Cons b bs)
    have factor: "(Poly_Mapping.single (Word (b#bs)) 1 :: 'k weyl_free) =
      Poly_Mapping.single (Word [b]) 1 * Poly_Mapping.single (Word bs) 1"
      by (simp only: free_mult_single mult_1_left append_Cons append_Nil)
    show ?case by (simp only: factor hmult hgen Cons.IH universal_word_list.simps)
  qed
  have hsingle: "h (Poly_Mapping.single w c) = universal_free_eval R s g (Poly_Mapping.single w c)" for w c
  proof (cases w)
    case (Word bs)
    have factor: "(Poly_Mapping.single w c :: 'k weyl_free) = free_scalar c * Poly_Mapping.single w 1"
      by (simp only: free_scalar_def Poly_Mapping.mult_single add_0_left mult_1_right)
    show ?thesis
      by (subst factor; simp only: hmult scalars Word hword free_eval_mult free_eval_scalar
        free_eval_single universal_word_def weyl_word.case scalar_one scalar.S.l_one[OF word_list_closed])
  qed
  show ?thesis
  proof (rule ext)
    fix f :: "'k weyl_free"
    show "h f = universal_free_eval R s g f"
      by (induction f rule: free_induct) (simp_all only: hzero free_eval_zero hadd free_eval_add hsingle)
  qed
qed

text \<open>Uniqueness is equality of total functions because the source carrier
is UNIV; no corresponding full-carrier hypothesis is imposed on the target.\<close>

theorem free_universal_property:
  "\<exists>!h :: 'k weyl_free \<Rightarrow> 'a.
    h \<in> ring_hom free_ring R \<and> (\<forall>c. h (free_scalar c) = s c) \<and>
    h free_X = g False \<and> h free_Y = g True"
proof (rule ex1I[of _ "universal_free_eval R s g"])
  show "universal_free_eval R s g \<in> ring_hom free_ring R \<and>
    (\<forall>c. universal_free_eval R s g (free_scalar c) = s c) \<and>
    universal_free_eval R s g free_X = g False \<and> universal_free_eval R s g free_Y = g True"
    using free_eval_ring_hom free_eval_scalar free_eval_X free_eval_Y by blast
  fix h :: "'k weyl_free \<Rightarrow> 'a"
  assume h: "h \<in> ring_hom free_ring R \<and> (\<forall>c. h (free_scalar c) = s c) \<and>
    h free_X = g False \<and> h free_Y = g True"
  show "h = universal_free_eval R s g"
    by (rule free_eval_unique) (use h in auto)
qed

end
end
