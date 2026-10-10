theory Bivariate_Polynomial
  imports "PBW_Finite_Coordinates"
begin

text \<open>The outer polynomial variable is Y, the inner one X. Pair (i,j)
means \<^verbatim>\<open>X^i\<close> \<^verbatim>\<open>Y^j\<close>. The ordinary multiplication here is commutative symbol
multiplication, never multiplication of polynomial operators.\<close>

type_synonym 'a bivariate = "'a poly poly"
definition biv_coeff :: "'a::field bivariate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "biv_coeff p i j = coeff (coeff p j) i"
definition biv_monom :: "'a::field \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a bivariate" where
  "biv_monom c i j = monom (monom c i) j"
definition biv_support :: "'a::field bivariate \<Rightarrow> (nat \<times> nat) set" where
  "biv_support p = {u. biv_coeff p (fst u) (snd u) \<noteq> 0}"
definition pair_exponent :: "nat \<times> nat \<Rightarrow> bool \<Rightarrow> nat" where
  "pair_exponent u b = (if b then snd u else fst u)"
definition exponent_pair :: "(bool \<Rightarrow> nat) \<Rightarrow> nat \<times> nat" where
  "exponent_pair e = (e False, e True)"
lemma exponent_pair_inverse [simp]: "exponent_pair (pair_exponent u) = u"
  by (simp add: exponent_pair_def pair_exponent_def)
lemma pair_exponent_inverse [simp]: "pair_exponent (exponent_pair e) = e"
  by (rule ext) (simp add: exponent_pair_def pair_exponent_def split: bool.split)
lemma pair_exponent_bijective: "bij pair_exponent"
  by (rule bijI) (metis exponent_pair_inverse injI, metis pair_exponent_inverse surjI)
lemma biv_eqI:
  "(\<And>i j. biv_coeff p i j = biv_coeff q i j) \<Longrightarrow> p = q"
  unfolding biv_coeff_def by (intro poly_eqI) auto
lemma biv_coeff_zero [simp]: "biv_coeff 0 i j = 0"
  by (simp add: biv_coeff_def)
lemma biv_coeff_add [simp]: "biv_coeff (p + q) i j = biv_coeff p i j + biv_coeff q i j"
  by (simp add: biv_coeff_def)
lemma biv_coeff_diff [simp]: "biv_coeff (p - q) i j = biv_coeff p i j - biv_coeff q i j"
  by (simp add: biv_coeff_def)
lemma biv_coeff_smult [simp]:
  "biv_coeff (smult [:c:] p) i j = c * biv_coeff p i j"
  by (simp add: biv_coeff_def)
lemma biv_coeff_sum:
  "biv_coeff (\<Sum>u\<in>S. f u) i j = (\<Sum>u\<in>S. biv_coeff (f u) i j)"
  by (simp add: biv_coeff_def coeff_sum)
lemma biv_coeff_monom [simp]:
  "biv_coeff (biv_monom c a b) i j = (if i = a \<and> j = b then c else 0)"
  by (auto simp: biv_coeff_def biv_monom_def coeff_monom)
lemma biv_monom_zero [simp]: "biv_monom 0 a b = 0"
  by (simp add: biv_monom_def)
lemma biv_monom_eq_zero [simp]: "biv_monom c a b = 0 \<longleftrightarrow> c = 0"
  by (auto simp: biv_monom_def)
lemma biv_mult_monom:
  "biv_monom c a b * biv_monom d e f = biv_monom (c*d) (a+e) (b+f)"
  by (simp add: biv_monom_def mult_monom)
lemma biv_support_zero [simp]: "biv_support 0 = {}"
  by (simp add: biv_support_def)
lemma finite_biv_support [simp]: "finite (biv_support p)"
proof -
  have sub: "biv_support p \<subseteq> (\<Union>j\<in>{..degree p}. (\<lambda>i. (i,j)) ` {..degree (coeff p j)})"
  proof
    fix u assume "u \<in> biv_support p"
    then have nz: "coeff (coeff p (snd u)) (fst u) \<noteq> 0"
      by (simp add: biv_support_def biv_coeff_def)
    have inner: "fst u \<le> degree (coeff p (snd u))" by (rule le_degree[OF nz])
    have outer_nz: "coeff p (snd u) \<noteq> 0" using nz by auto
    have outer: "snd u \<le> degree p" by (rule le_degree[OF outer_nz])
    show "u \<in> (\<Union>j\<in>{..degree p}. (\<lambda>i. (i,j)) ` {..degree (coeff p j)})"
      using inner outer by (rule_tac UN_I[of "snd u"]) (auto intro!: image_eqI[where x="fst u"])
  qed
  show ?thesis by (rule finite_subset[OF sub]) simp
qed
lemma biv_sum_monom_coeff:
  assumes "finite S"
  shows "biv_coeff (\<Sum>u\<in>S. biv_monom (c u) (fst u) (snd u)) i j =
    (if (i,j) \<in> S then c (i,j) else 0)"
proof -
  have eq: "(i = fst u \<and> j = snd u) \<longleftrightarrow> u = (i,j)" for u by (cases u) auto
  show ?thesis using assms by (simp add: biv_coeff_sum eq sum.delta)
qed
lemma biv_reconstruct:
  "(\<Sum>u\<in>biv_support p. biv_monom (biv_coeff p (fst u) (snd u)) (fst u) (snd u)) = p"
  by (rule biv_eqI) (simp only: biv_sum_monom_coeff[OF finite_biv_support]; simp add: biv_support_def)
lemma biv_support_sum_monom:
  assumes "finite S"
  shows "biv_support (\<Sum>u\<in>S. biv_monom (c u) (fst u) (snd u)) = {u\<in>S. c u \<noteq> 0}"
  using assms by (auto simp: biv_support_def biv_sum_monom_coeff)

end
