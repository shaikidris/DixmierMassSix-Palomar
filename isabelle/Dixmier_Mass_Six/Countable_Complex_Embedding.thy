theory Countable_Complex_Embedding
  imports Countable_Carrier_Enumeration
    "Transcendental_Carrier_Extension"
    "Rational_Carrier_Seed"
    "Typed_Field_Descent"
begin

text \<open>The one-generator premise of the generic enumeration theorem is
fully discharged here. The ambient source type need not be countable.\<close>
theorem exists_countable_carrier_embedding_to_complex:
  fixes E :: "'k::field_char_0 set"
  assumes closed: "division_subring_on E" and count: "countable E"
  shows "\<exists>f::'k \<Rightarrow> complex. dixmier_carrier_field_embedding E f \<and>
    (\<forall>q::rat. f (of_rat q) = of_rat q) \<and> (\<forall>x. x \<notin> E \<longrightarrow> f x=0)"
proof -
  let ?S0 = "range (of_rat::rat \<Rightarrow> 'k)"
  have seed: "?S0 \<subseteq> E" by (rule division_carrier_contains_rationals[OF closed])
  have conditional: "\<exists>g::'k \<Rightarrow> complex. dixmier_carrier_field_embedding E g \<and>
    (\<forall>x\<in>?S0. g x=rational_seed_map x) \<and> (\<forall>x. x \<notin> E \<longrightarrow> g x=0)"
  proof (rule conditional_countable_carrier_extension[OF closed count seed rational_seed_embedding])
    fix S :: "'k set" and F :: "'k \<Rightarrow> complex" and a :: 'k
    assume "S \<subseteq> E" "division_subring_on S" and countS: "countable S"
      and embS: "dixmier_carrier_field_embedding S F" and "a \<in> E"
    show "\<exists>G::'k \<Rightarrow> complex. dixmier_carrier_field_embedding (division_closure (insert a S)) G \<and>
      (\<forall>x\<in>S. G x=F x)"
      by (rule countable_carrier_one_generator_extension[OF embS countS])
  qed
  obtain f :: "'k \<Rightarrow> complex" where emb: "dixmier_carrier_field_embedding E f"
    and agrees: "\<forall>x\<in>?S0. f x=rational_seed_map x"
    and outside: "\<forall>x. x \<notin> E \<longrightarrow> f x=0"
    using conditional by blast
  have rat: "f (of_rat q)=of_rat q" for q :: rat
  proof -
    have qr: "(of_rat q::'k) \<in> ?S0" by (rule rangeI)
    have "f (of_rat q)=rational_seed_map (of_rat q::'k)" by (rule agrees[rule_format, OF qr])
    also have "...=(of_rat q::complex)" by (rule rational_seed_equation)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule exI[of _ f], intro conjI)
    show "dixmier_carrier_field_embedding E f" by (rule emb)
    show "\<forall>q::rat. f (of_rat q)=of_rat q" by (intro allI rat)
    show "\<forall>x. x \<notin> E \<longrightarrow> f x=0" by (rule outside)
  qed
qed

corollary countable_carrier_embedding_exists:
  fixes E :: "'k::field_char_0 set"
  assumes "division_subring_on E" "countable E"
  shows "\<exists>f::'k \<Rightarrow> complex. dixmier_carrier_field_embedding E f"
  using exists_countable_carrier_embedding_to_complex[OF assms] by blast

text \<open>The whole-type specialization is the retained countable-field F3
contract: a unital field embedding commuting with the canonical rational maps.\<close>
theorem exists_rational_field_embedding_to_complex_of_countable:
  assumes count: "countable (UNIV::'k::field_char_0 set)"
  shows "\<exists>f::'k \<Rightarrow> complex. dixmier_field_embedding f \<and>
    (\<forall>q::rat. f (of_rat q)=of_rat q)"
proof -
  have closed: "division_subring_on (UNIV::'k set)" by (simp add: division_subring_on_def)
  obtain f :: "'k \<Rightarrow> complex" where emb: "dixmier_carrier_field_embedding UNIV f"
    and rat: "\<forall>q::rat. f (of_rat q)=of_rat q"
    using exists_countable_carrier_embedding_to_complex[OF closed count] by blast
  interpret e: dixmier_carrier_field_embedding UNIV f by (rule emb)
  have typed: "dixmier_field_embedding f"
  proof
    show "f 1=1" by (rule e.map_one)
    show "f(a+b)=f a+f b" for a b by (rule e.map_add_on) simp_all
    show "f(a*b)=f a*f b" for a b by (rule e.map_mult_on) simp_all
    show "inj f" by (rule e.injective_on)
  qed
  show ?thesis by (rule exI[of _ f]) (simp only: typed rat simp_thms)
qed

corollary exists_countable_rational_algebra_embedding:
  assumes count: "countable (UNIV::'k::field_char_0 set)"
  shows "\<exists>f::'k \<Rightarrow> complex. dixmier_field_embedding f \<and>
    (\<forall>q::rat. f (of_rat q)=of_rat q) \<and>
    (\<forall>q::rat. \<forall>x::'k. f (of_rat q*x)=of_rat q*f x)"
proof -
  obtain f :: "'k \<Rightarrow> complex" where emb: "dixmier_field_embedding f"
    and rat: "\<forall>q::rat. f (of_rat q)=of_rat q"
    using exists_rational_field_embedding_to_complex_of_countable[OF count] by blast
  interpret e: dixmier_field_embedding f by (rule emb)
  have scalar: "f (of_rat q*x)=of_rat q*f x" for q :: rat and x :: 'k
    by (simp only: e.map_mult rat[rule_format])
  show ?thesis
  proof (rule exI[of _ f], intro conjI)
    show "dixmier_field_embedding f" by (rule emb)
    show "\<forall>q::rat. f (of_rat q)=of_rat q" by (rule rat)
    show "\<forall>q::rat. \<forall>x::'k. f (of_rat q*x)=of_rat q*f x" by (intro allI scalar)
  qed
qed

end
