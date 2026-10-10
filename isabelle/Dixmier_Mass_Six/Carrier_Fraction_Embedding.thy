theory Carrier_Fraction_Embedding
  imports "Carrier_Field_Embedding"
begin

text \<open>A fraction carrier is a set of values in the existing ambient field.
The input carrier is only a subring, and need not be closed under inverse.\<close>

definition unital_subring_on :: "'k::field set \<Rightarrow> bool" where
  "unital_subring_on A \<longleftrightarrow>
    0 \<in> A \<and> 1 \<in> A \<and>
    (\<forall>a\<in>A. -a \<in> A) \<and>
    (\<forall>a\<in>A. \<forall>b\<in>A. a+b \<in> A \<and> a*b \<in> A)"

definition fraction_carrier :: "'k::field set \<Rightarrow> 'k set" where
  "fraction_carrier A = {x. \<exists>a\<in>A. \<exists>b\<in>A. b \<noteq> 0 \<and> x=a/b}"

lemma fraction_carrierI:
  "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a/b \<in> fraction_carrier A"
  unfolding fraction_carrier_def by blast

lemma fraction_carrierE:
  assumes "x \<in> fraction_carrier A"
  obtains a b where "a \<in> A" "b \<in> A" "b \<noteq> 0" "x=a/b"
  using assms unfolding fraction_carrier_def by blast

locale dixmier_unital_subring =
  fixes A :: "'k::field set"
  assumes ring_closed: "unital_subring_on A"
begin

lemma A_zero [simp]: "0 \<in> A"
  using ring_closed unfolding unital_subring_on_def by blast
lemma A_one [simp]: "1 \<in> A"
  using ring_closed unfolding unital_subring_on_def by blast
lemma A_neg: "a \<in> A \<Longrightarrow> -a \<in> A"
  using ring_closed unfolding unital_subring_on_def by blast
lemma A_add: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a+b \<in> A"
  using ring_closed unfolding unital_subring_on_def by blast
lemma A_mult: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a*b \<in> A"
  using ring_closed unfolding unital_subring_on_def by blast
lemma A_diff: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a-b \<in> A"
  unfolding diff_conv_add_uminus by (intro A_add A_neg)

lemma fraction_carrier_generator:
  assumes "a \<in> A"
  shows "a \<in> fraction_carrier A"
proof -
  have "a/1 \<in> fraction_carrier A"
    by (rule fraction_carrierI[OF assms A_one]) simp
  then show ?thesis by simp
qed
lemma fraction_carrier_contains: "A \<subseteq> fraction_carrier A"
  using fraction_carrier_generator by blast
lemma fraction_carrier_zero [simp]: "0 \<in> fraction_carrier A"
  by (rule fraction_carrier_generator[OF A_zero])
lemma fraction_carrier_one [simp]: "1 \<in> fraction_carrier A"
  by (rule fraction_carrier_generator[OF A_one])

lemma fraction_carrier_neg:
  assumes "x \<in> fraction_carrier A"
  shows "-x \<in> fraction_carrier A"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and nz: "b \<noteq> 0" and x: "x=a/b"
    using assms by (rule fraction_carrierE)
  have "(-a)/b \<in> fraction_carrier A"
    by (rule fraction_carrierI[OF A_neg[OF a] b nz])
  then show ?thesis by (simp add: x)
qed

lemma fraction_carrier_inverse:
  assumes "x \<in> fraction_carrier A"
  shows "inverse x \<in> fraction_carrier A"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and nz: "b \<noteq> 0" and x: "x=a/b"
    using assms by (rule fraction_carrierE)
  show ?thesis
  proof (cases "a=0")
    case True then show ?thesis by (simp add: x)
  next
    case False
    have "b/a \<in> fraction_carrier A"
      by (rule fraction_carrierI[OF b a False])
    then show ?thesis by (simp add: x)
  qed
qed

lemma fraction_carrier_add:
  assumes "x \<in> fraction_carrier A" "y \<in> fraction_carrier A"
  shows "x+y \<in> fraction_carrier A"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using assms(1) by (rule fraction_carrierE)
  obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0" and y: "y=c/d"
    using assms(2) by (rule fraction_carrierE)
  have numerator: "a*d+c*b \<in> A"
    by (intro A_add A_mult a b c d)
  have denominator: "b*d \<in> A" by (rule A_mult[OF b d])
  have nonzero: "b*d \<noteq> 0" using bnz dnz by simp
  have "(a*d+c*b)/(b*d) \<in> fraction_carrier A"
    by (rule fraction_carrierI[OF numerator denominator nonzero])
  then show ?thesis by (simp only: x y add_frac_eq[OF bnz dnz])
qed

lemma fraction_carrier_mult:
  assumes "x \<in> fraction_carrier A" "y \<in> fraction_carrier A"
  shows "x*y \<in> fraction_carrier A"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using assms(1) by (rule fraction_carrierE)
  obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0" and y: "y=c/d"
    using assms(2) by (rule fraction_carrierE)
  have numerator: "a*c \<in> A" by (rule A_mult[OF a c])
  have denominator: "b*d \<in> A" by (rule A_mult[OF b d])
  have nonzero: "b*d \<noteq> 0" using bnz dnz by simp
  have "(a*c)/(b*d) \<in> fraction_carrier A"
    by (rule fraction_carrierI[OF numerator denominator nonzero])
  then show ?thesis by (simp add: x y divide_inverse ac_simps)
qed

lemma fraction_carrier_is_division_subring:
  "division_subring_on (fraction_carrier A)"
  unfolding division_subring_on_def
  by (auto intro: fraction_carrier_neg fraction_carrier_inverse
      fraction_carrier_add fraction_carrier_mult)

lemma fraction_carrier_eq_division_closure:
  "fraction_carrier A = division_closure A"
proof (rule subset_antisym)
  show "fraction_carrier A \<subseteq> division_closure A"
  proof
    fix x assume "x \<in> fraction_carrier A"
    then obtain a b where a: "a \<in> A" and b: "b \<in> A" and x: "x=a/b"
      by (rule fraction_carrierE)
    have "a \<in> division_closure A" by (rule division_closure_generator[OF a])
    moreover have "inverse b \<in> division_closure A"
      by (rule division_closure_inverse[OF division_closure_generator[OF b]])
    ultimately show "x \<in> division_closure A"
      unfolding x divide_inverse by (rule division_closure_mult)
  qed
  show "division_closure A \<subseteq> fraction_carrier A"
    by (rule division_closure_least[OF fraction_carrier_is_division_subring fraction_carrier_contains])
qed

end

locale dixmier_carrier_ring_embedding = dixmier_unital_subring A
  for A :: "'k::field set" +
  fixes h :: "'k \<Rightarrow> 'l::field"
  assumes map_one: "h 1 = 1"
    and map_add_on: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> h (a+b) = h a+h b"
    and map_mult_on: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> h (a*b) = h a*h b"
    and injective_on: "inj_on h A"
begin

lemma map_zero [simp]: "h 0 = 0"
proof -
  have "h 0 + 0 = h 0 + h 0" using map_add_on[OF A_zero A_zero] by simp
  then show ?thesis by (simp only: add_left_cancel)
qed
lemma map_eq_zero_on:
  assumes a: "a \<in> A"
  shows "h a = 0 \<longleftrightarrow> a=0"
proof
  assume "h a=0"
  then have eq: "h a=h 0" by simp
  show "a=0" by (rule inj_onD[OF injective_on eq a A_zero])
next
  assume "a=0"
  then show "h a=0" by simp
qed
lemma map_neg_on:
  assumes a: "a \<in> A"
  shows "h (-a) = -h a"
proof -
  have "h a + h (-a) = 0"
    using map_add_on[OF a A_neg[OF a]] by simp
  then show ?thesis by (simp only: add_eq_0_iff)
qed

text \<open>Prove both directions before making any choice of a fraction value.\<close>
lemma mapped_ratio_eq_iff:
  assumes a: "a \<in> A" and b: "b \<in> A" and c: "c \<in> A" and d: "d \<in> A"
    and bnz: "b \<noteq> 0" and dnz: "d \<noteq> 0"
  shows "(h a / h b = h c / h d) \<longleftrightarrow> (a/b=c/d)"
proof -
  have hbnz: "h b \<noteq> 0" using map_eq_zero_on[OF b] bnz by simp
  have hdnz: "h d \<noteq> 0" using map_eq_zero_on[OF d] dnz by simp
  have cross: "(h (a*d)=h (c*b)) \<longleftrightarrow> (a*d=c*b)"
  proof
    assume eq: "h (a*d)=h (c*b)"
    show "a*d=c*b"
      by (rule inj_onD[OF injective_on eq A_mult[OF a d] A_mult[OF c b]])
  next
    assume "a*d=c*b"
    then show "h (a*d)=h (c*b)" by simp
  qed
  have mapped_cross: "(h a*h d=h c*h b) \<longleftrightarrow> (a*d=c*b)"
    using cross by (simp only: map_mult_on[OF a d] map_mult_on[OF c b])
  show ?thesis
    by (simp only: frac_eq_eq[OF hbnz hdnz] frac_eq_eq[OF bnz dnz] mapped_cross)
qed

lemma mapped_ratio_unique:
  assumes "x \<in> fraction_carrier A"
  shows "\<exists>!y. \<exists>a\<in>A. \<exists>b\<in>A. b \<noteq> 0 \<and> x=a/b \<and> y=h a/h b"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using assms by (rule fraction_carrierE)
  show ?thesis
  proof (rule ex1I[of _ "h a/h b"])
    show "\<exists>a'\<in>A. \<exists>b'\<in>A. b' \<noteq> 0 \<and> x=a'/b' \<and> h a/h b=h a'/h b'"
      using a b bnz x by blast
    fix y assume "\<exists>c\<in>A. \<exists>d\<in>A. d \<noteq> 0 \<and> x=c/d \<and> y=h c/h d"
    then obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0"
      and xc: "x=c/d" and y: "y=h c/h d" by blast
    have "h c/h d=h a/h b"
      using mapped_ratio_eq_iff[OF c d a b dnz bnz] x xc by simp
    then show "y=h a/h b" by (simp only: y)
  qed
qed

definition fraction_extension :: "'k \<Rightarrow> 'l" where
  "fraction_extension x = (if x \<in> fraction_carrier A then
    (THE y. \<exists>a\<in>A. \<exists>b\<in>A. b \<noteq> 0 \<and> x=a/b \<and> y=h a/h b) else 0)"

lemma fraction_extension_outside:
  "x \<notin> fraction_carrier A \<Longrightarrow> fraction_extension x=0"
  by (simp add: fraction_extension_def)

lemma fraction_extension_ratio:
  assumes a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0"
  shows "fraction_extension (a/b) = h a/h b"
proof -
  have member: "a/b \<in> fraction_carrier A" by (rule fraction_carrierI[OF a b bnz])
  have chosen_ratio: "(THE y. \<exists>c\<in>A. \<exists>d\<in>A. d \<noteq> 0 \<and> a/b=c/d \<and> y=h c/h d) = h a/h b"
  proof (rule the1_equality[OF mapped_ratio_unique[OF member]])
    show "\<exists>c\<in>A. \<exists>d\<in>A. d \<noteq> 0 \<and> a/b=c/d \<and> h a/h b=h c/h d"
      using a b bnz by blast
  qed
  show ?thesis by (simp only: fraction_extension_def if_P[OF member] chosen_ratio)
qed

lemma fraction_extension_agrees:
  assumes "a \<in> A"
  shows "fraction_extension a=h a"
  using fraction_extension_ratio[OF assms A_one] by (simp add: map_one)

lemma fraction_extension_one: "fraction_extension 1=1"
  using fraction_extension_agrees[OF A_one] map_one by simp

lemma fraction_extension_add:
  assumes "x \<in> fraction_carrier A" "y \<in> fraction_carrier A"
  shows "fraction_extension (x+y)=fraction_extension x+fraction_extension y"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using assms(1) by (rule fraction_carrierE)
  obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0" and y: "y=c/d"
    using assms(2) by (rule fraction_carrierE)
  have ad: "a*d \<in> A" by (rule A_mult[OF a d])
  have cb: "c*b \<in> A" by (rule A_mult[OF c b])
  have numerator: "a*d+c*b \<in> A" by (rule A_add[OF ad cb])
  have denominator: "b*d \<in> A" by (rule A_mult[OF b d])
  have nonzero: "b*d \<noteq> 0" using bnz dnz by simp
  have hbnz: "h b \<noteq> 0" using map_eq_zero_on[OF b] bnz by simp
  have hdnz: "h d \<noteq> 0" using map_eq_zero_on[OF d] dnz by simp
  have "fraction_extension (x+y)=h (a*d+c*b)/h (b*d)"
    unfolding x y add_frac_eq[OF bnz dnz]
    by (rule fraction_extension_ratio[OF numerator denominator nonzero])
  also have "...=(h a*h d+h c*h b)/(h b*h d)"
    by (simp only: map_add_on[OF ad cb] map_mult_on[OF a d]
        map_mult_on[OF c b] map_mult_on[OF b d])
  also have "...=h a/h b+h c/h d"
    by (rule add_frac_eq[OF hbnz hdnz, symmetric])
  also have "...=fraction_extension x+fraction_extension y"
    by (simp only: x y fraction_extension_ratio[OF a b bnz] fraction_extension_ratio[OF c d dnz])
  finally show ?thesis .
qed

lemma fraction_extension_mult:
  assumes "x \<in> fraction_carrier A" "y \<in> fraction_carrier A"
  shows "fraction_extension (x*y)=fraction_extension x*fraction_extension y"
proof -
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using assms(1) by (rule fraction_carrierE)
  obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0" and y: "y=c/d"
    using assms(2) by (rule fraction_carrierE)
  have numerator: "a*c \<in> A" by (rule A_mult[OF a c])
  have denominator: "b*d \<in> A" by (rule A_mult[OF b d])
  have nonzero: "b*d \<noteq> 0" using bnz dnz by simp
  have product: "x*y=(a*c)/(b*d)" by (simp add: x y divide_inverse ac_simps)
  have "fraction_extension (x*y)=h (a*c)/h (b*d)"
    unfolding product by (rule fraction_extension_ratio[OF numerator denominator nonzero])
  also have "...=(h a*h c)/(h b*h d)"
    by (simp only: map_mult_on[OF a c] map_mult_on[OF b d])
  also have "...=(h a/h b)*(h c/h d)" by (simp add: divide_inverse ac_simps)
  also have "...=fraction_extension x*fraction_extension y"
    by (simp only: x y fraction_extension_ratio[OF a b bnz] fraction_extension_ratio[OF c d dnz])
  finally show ?thesis .
qed

lemma fraction_extension_injective:
  "inj_on fraction_extension (fraction_carrier A)"
proof (rule inj_onI)
  fix x y assume xA: "x \<in> fraction_carrier A" and yA: "y \<in> fraction_carrier A"
    and eq: "fraction_extension x=fraction_extension y"
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and x: "x=a/b"
    using xA by (rule fraction_carrierE)
  obtain c d where c: "c \<in> A" and d: "d \<in> A" and dnz: "d \<noteq> 0" and y: "y=c/d"
    using yA by (rule fraction_carrierE)
  have "h a/h b=h c/h d"
    using eq by (simp only: x y fraction_extension_ratio[OF a b bnz] fraction_extension_ratio[OF c d dnz])
  then have "a/b=c/d" using mapped_ratio_eq_iff[OF a b c d bnz dnz] by blast
  then show "x=y" by (simp only: x y)
qed

lemma fraction_extension_embedding:
  "dixmier_carrier_field_embedding (fraction_carrier A) fraction_extension"
  by unfold_locales
    (fact fraction_carrier_is_division_subring fraction_extension_one
      fraction_extension_add fraction_extension_mult fraction_extension_injective)+

lemma division_closure_extension_embedding:
  "dixmier_carrier_field_embedding (division_closure A) fraction_extension"
  using fraction_extension_embedding by (simp only: fraction_carrier_eq_division_closure)

theorem exists_fraction_extension:
  "\<exists>g. dixmier_carrier_field_embedding (division_closure A) g \<and>
    (\<forall>a\<in>A. g a=h a) \<and>
    (\<forall>a\<in>A. \<forall>b\<in>A. b \<noteq> 0 \<longrightarrow> g (a/b)=h a/h b) \<and>
    (\<forall>x. x \<notin> division_closure A \<longrightarrow> g x=0)"
  by (intro exI[of _ fraction_extension] conjI division_closure_extension_embedding ballI allI impI)
    (auto intro: fraction_extension_agrees fraction_extension_ratio
      simp: fraction_extension_outside fraction_carrier_eq_division_closure)

lemma fraction_extension_unique_on:
  assumes g: "dixmier_carrier_field_embedding (division_closure A) g"
    and agree: "\<And>a. a \<in> A \<Longrightarrow> g a=h a"
    and x: "x \<in> division_closure A"
  shows "g x=fraction_extension x"
proof -
  interpret g: dixmier_carrier_field_embedding "division_closure A" g by (fact g)
  obtain a b where a: "a \<in> A" and b: "b \<in> A" and bnz: "b \<noteq> 0" and rep: "x=a/b"
    using x unfolding fraction_carrier_eq_division_closure[symmetric] by (rule fraction_carrierE)
  have ac: "a \<in> division_closure A" by (rule division_closure_generator[OF a])
  have bc: "b \<in> division_closure A" by (rule division_closure_generator[OF b])
  have "g (a/b)=g a / g b"
    unfolding divide_inverse
    by (simp only: g.map_mult_on[OF ac g.E_inverse[OF bc]] g.map_inverse_on[OF bc])
  then show ?thesis
    by (simp only: rep agree[OF a] agree[OF b] fraction_extension_ratio[OF a b bnz])
qed

end

text \<open>An unlocalized interface with exactly the stated input assumptions.\<close>
theorem carrier_fraction_embedding_exists:
  fixes A :: "'k::field set" and h :: "'k \<Rightarrow> 'l::field"
  assumes A: "unital_subring_on A"
    and one: "h 1=1"
    and add: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> h (a+b)=h a+h b"
    and mult: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> h (a*b)=h a*h b"
    and inj: "inj_on h A"
  shows "fraction_carrier A=division_closure A \<and>
    (\<exists>g. dixmier_carrier_field_embedding (division_closure A) g \<and>
      (\<forall>a\<in>A. g a=h a) \<and>
      (\<forall>a\<in>A. \<forall>b\<in>A. b \<noteq> 0 \<longrightarrow> g (a/b)=h a/h b) \<and>
      (\<forall>x. x \<notin> division_closure A \<longrightarrow> g x=0))"
proof -
  interpret h: dixmier_carrier_ring_embedding A h
    by unfold_locales (fact A one add mult inj)+
  show ?thesis using h.fraction_carrier_eq_division_closure h.exists_fraction_extension by blast
qed

end
