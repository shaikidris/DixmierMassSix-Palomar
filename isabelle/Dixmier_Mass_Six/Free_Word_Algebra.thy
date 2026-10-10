theory Free_Word_Algebra
  imports "HOL-Library.Poly_Mapping" "HOL-Algebra.RingHom"
begin

text \<open>A fresh noncommutative additive monoid of words. False denotes X
and True denotes Y. Addition of words is concatenation, not a commutative
exponent-vector operation.\<close>

datatype weyl_word = Word "bool list"

instantiation weyl_word :: monoid_add
begin

definition zero_weyl_word :: weyl_word where "0 = Word []"
definition plus_weyl_word :: "weyl_word \<Rightarrow> weyl_word \<Rightarrow> weyl_word" where
  "u + v = (case u of Word us \<Rightarrow> case v of Word vs \<Rightarrow> Word (us @ vs))"

instance
proof
  fix a b c :: weyl_word
  show "a + b + c = a + (b + c)"
    by (cases a; cases b; cases c) (simp add: plus_weyl_word_def)
  show "0 + a = a"
    by (cases a) (simp add: zero_weyl_word_def plus_weyl_word_def)
  show "a + 0 = a"
    by (cases a) (simp add: zero_weyl_word_def plus_weyl_word_def)
qed

end

lemma free_word_add [simp]: "Word u + Word v = Word (u @ v)"
  by (simp add: plus_weyl_word_def)
lemma free_word_zero: "(0 :: weyl_word) = Word []"
  by (rule zero_weyl_word_def)

type_synonym 'k weyl_free = "(weyl_word, 'k) poly_mapping"

definition free_scalar :: "'k::field \<Rightarrow> 'k weyl_free" where
  "free_scalar c = Poly_Mapping.single 0 c"
definition free_X :: "'k::field weyl_free" where
  "free_X = Poly_Mapping.single (Word [False]) 1"
definition free_Y :: "'k::field weyl_free" where
  "free_Y = Poly_Mapping.single (Word [True]) 1"
definition weyl_relation :: "'k::field weyl_free" where
  "weyl_relation = free_Y * free_X - free_X * free_Y - 1"

lemma free_mult_single:
  "Poly_Mapping.single (Word u) (a :: 'k::field) * Poly_Mapping.single (Word v) b =
   Poly_Mapping.single (Word (u @ v)) (a * b)"
  by (simp add: Poly_Mapping.mult_single)

lemma free_single_expansion:
  "f = (\<Sum>w\<in>Poly_Mapping.keys f. Poly_Mapping.single w (Poly_Mapping.lookup f w))"
  for f :: "'k::field weyl_free"
  by (rule poly_mapping_eqI)
     (simp add: Poly_Mapping.lookup_sum Poly_Mapping.lookup_single when_def
       sum.delta Poly_Mapping.in_keys_iff)

lemma free_induct [case_names zero add single]:
  assumes zero: "P 0"
    and add: "\<And>f g. P f \<Longrightarrow> P g \<Longrightarrow> P (f + g)"
    and single: "\<And>w c. P (Poly_Mapping.single w c)"
  shows "P (f :: 'k::field weyl_free)"
proof -
  have "P (\<Sum>w\<in>S. Poly_Mapping.single w (Poly_Mapping.lookup f w))" if "finite S" for S
    using that by (induction S rule: finite_induct) (auto intro: zero add single)
  then show ?thesis
    by (subst free_single_expansion) simp
qed

lemma free_scalar_zero [simp]: "free_scalar 0 = 0"
  by (simp add: free_scalar_def)
lemma free_scalar_one [simp]: "free_scalar 1 = 1"
  by (simp add: free_scalar_def Poly_Mapping.single_one)
lemma free_scalar_add:
  "free_scalar (a+b) = free_scalar a + free_scalar b"
  by (simp add: free_scalar_def Poly_Mapping.single_add)
lemma free_scalar_mult:
  "free_scalar (a*b) = free_scalar a * free_scalar b"
  by (simp add: free_scalar_def Poly_Mapping.mult_single)
lemma free_scalar_central:
  "free_scalar c * f = f * free_scalar c"
  for f :: "'k::field weyl_free"
  by (induction f rule: free_induct)
     (simp_all add: free_scalar_def Poly_Mapping.mult_single algebra_simps)

lemma free_XY_ne_YX:
  "free_X * free_Y \<noteq> (free_Y * free_X :: 'k::field weyl_free)"
proof
  assume eq: "free_X * free_Y = (free_Y * free_X :: 'k weyl_free)"
  have "Poly_Mapping.lookup (free_X * free_Y :: 'k weyl_free) (Word [False,True]) =
        Poly_Mapping.lookup (free_Y * free_X :: 'k weyl_free) (Word [False,True])"
    using eq by simp
  then show False
    by (simp add: free_X_def free_Y_def free_mult_single Poly_Mapping.lookup_single when_def)
qed

text \<open>The record bridge is deliberately noncommutative. The official
\<^verbatim>\<open>ring_from_type_algebra\<close> theorem has a \<^verbatim>\<open>comm_ring_1\<close> restriction.\<close>

definition nc_type_ring :: "'a::ring_1 ring" where
  "nc_type_ring = \<lparr>carrier = UNIV, monoid.mult = (*), monoid.one = 1, ring.zero = 0, ring.add = (+)\<rparr>"

lemma nc_type_ring_is_ring: "ring (nc_type_ring :: 'a::ring_1 ring)"
proof (rule ringI)
  show "abelian_group (nc_type_ring :: 'a ring)"
    by (rule abelian_groupI) (auto simp: nc_type_ring_def add.assoc add.commute add_eq_0_iff)
  show "Group.monoid (nc_type_ring :: 'a ring)"
    by (rule monoidI) (auto simp: nc_type_ring_def mult.assoc)
  show "\<And>x y z. x \<in> carrier (nc_type_ring :: 'a ring) \<Longrightarrow>
    y \<in> carrier nc_type_ring \<Longrightarrow> z \<in> carrier nc_type_ring \<Longrightarrow>
    monoid.mult nc_type_ring (ring.add nc_type_ring x y) z =
    ring.add nc_type_ring (monoid.mult nc_type_ring x z) (monoid.mult nc_type_ring y z)"
    by (simp add: nc_type_ring_def algebra_simps)
  show "\<And>x y z. x \<in> carrier (nc_type_ring :: 'a ring) \<Longrightarrow>
    y \<in> carrier nc_type_ring \<Longrightarrow> z \<in> carrier nc_type_ring \<Longrightarrow>
    monoid.mult nc_type_ring z (ring.add nc_type_ring x y) =
    ring.add nc_type_ring (monoid.mult nc_type_ring z x) (monoid.mult nc_type_ring z y)"
    by (simp add: nc_type_ring_def algebra_simps)
qed

definition free_ring :: "'k::field weyl_free ring" where
  "free_ring = nc_type_ring"
lemma free_ring_is_ring: "ring (free_ring :: 'k::field weyl_free ring)"
  by (simp add: free_ring_def nc_type_ring_is_ring)
lemma free_ring_simps [simp]:
  "carrier (free_ring :: 'k::field weyl_free ring) = UNIV"
  "monoid.mult (free_ring :: 'k::field weyl_free ring) = (*)"
  "ring.add (free_ring :: 'k::field weyl_free ring) = (+)"
  "monoid.one (free_ring :: 'k::field weyl_free ring) = 1"
  "ring.zero (free_ring :: 'k::field weyl_free ring) = 0"
  by (simp_all add: free_ring_def nc_type_ring_def)

definition weyl_relation_ideal :: "'k::field weyl_free set" where
  "weyl_relation_ideal = genideal free_ring {weyl_relation}"
lemma weyl_relation_ideal_is_ideal:
  "ideal (weyl_relation_ideal :: 'k::field weyl_free set) free_ring"
  unfolding weyl_relation_ideal_def
  by (rule ring.genideal_ideal[OF free_ring_is_ring]) simp
lemma weyl_relation_mem_ideal:
  "weyl_relation \<in> (weyl_relation_ideal :: 'k::field weyl_free set)"
  unfolding weyl_relation_ideal_def
  by (rule ring.genideal_self'[OF free_ring_is_ring]) simp

end
