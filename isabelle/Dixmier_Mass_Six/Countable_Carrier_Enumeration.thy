theory Countable_Carrier_Enumeration
  imports "Carrier_Embedding_Chain"
begin

primrec generated_carrier_stages :: "'k::field set \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow> nat \<Rightarrow> 'k set" where
  "generated_carrier_stages S0 e 0 = S0"
| "generated_carrier_stages S0 e (Suc n) = division_closure (insert (e n) (generated_carrier_stages S0 e n))"

primrec chosen_carrier_stage_maps :: "(nat \<Rightarrow> 'k::field set) \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow>
    ('k \<Rightarrow> 'l::field) \<Rightarrow> nat \<Rightarrow> 'k \<Rightarrow> 'l" where
  "chosen_carrier_stage_maps S e f0 0 = f0"
| "chosen_carrier_stage_maps S e f0 (Suc n) =
    (SOME g. dixmier_carrier_field_embedding (division_closure (insert (e n) (S n))) g \<and>
      (\<forall>x\<in>S n. g x = chosen_carrier_stage_maps S e f0 n x))"

lemma generated_carrier_stages_increasing:
  "generated_carrier_stages S0 e n \<subseteq> generated_carrier_stages S0 e (Suc n)"
  using division_closure_contains[of "insert (e n) (generated_carrier_stages S0 e n)"] by simp
lemma generated_carrier_stages_inside:
  assumes closed: "division_subring_on E" and seed: "S0 \<subseteq> E" and enumeration: "\<And>n. e n \<in> E"
  shows "generated_carrier_stages S0 e n \<subseteq> E"
proof (induction n)
  case 0 show ?case by (simp only: generated_carrier_stages.simps seed)
next
  case (Suc n)
  show ?case unfolding generated_carrier_stages.simps
    by (rule division_closure_least[OF closed]) (use Suc.IH enumeration[of n] in auto)
qed
lemma generated_carrier_stages_union:
  assumes closed: "division_subring_on E" and seed: "S0 \<subseteq> E" and enumeration: "range e=E"
  shows "(\<Union>n. generated_carrier_stages S0 e n)=E"
proof (rule subset_antisym)
  have en: "e n \<in> E" for n using enumeration by blast
  have inside: "generated_carrier_stages S0 e n \<subseteq> E" for n
  proof (rule generated_carrier_stages_inside)
    show "division_subring_on E" by (rule closed)
    show "S0 \<subseteq> E" by (rule seed)
    show "\<And>m. e m \<in> E" by (rule en)
  qed
  show "(\<Union>n. generated_carrier_stages S0 e n) \<subseteq> E"
    using inside by blast
next
  show "E \<subseteq> (\<Union>n. generated_carrier_stages S0 e n)"
  proof
    fix x assume "x \<in> E"
    then obtain n where x: "x=e n" using enumeration by blast
    have "x \<in> generated_carrier_stages S0 e (Suc n)"
      unfolding generated_carrier_stages.simps x by (rule division_closure_generator) simp
    then show "x \<in> (\<Union>n. generated_carrier_stages S0 e n)" by blast
  qed
qed

text \<open>This generic theorem is deliberately conditional on one-generator
extension. The later complex theorem discharges that premise.\<close>
theorem conditional_countable_carrier_extension:
  fixes E S0 :: "'k::field set" and f0 :: "'k \<Rightarrow> 'l::field"
  assumes closed: "division_subring_on E" and count: "countable E"
    and seed: "S0 \<subseteq> E" and initial: "dixmier_carrier_field_embedding S0 f0"
    and extend: "\<And>S F a. S \<subseteq> E \<Longrightarrow> division_subring_on S \<Longrightarrow> countable S \<Longrightarrow>
      dixmier_carrier_field_embedding S F \<Longrightarrow> a \<in> E \<Longrightarrow>
      \<exists>G::'k \<Rightarrow> 'l. dixmier_carrier_field_embedding (division_closure (insert a S)) G \<and>
        (\<forall>x\<in>S. G x=F x)"
  shows "\<exists>g::'k \<Rightarrow> 'l. dixmier_carrier_field_embedding E g \<and>
    (\<forall>x\<in>S0. g x=f0 x) \<and> (\<forall>x. x \<notin> E \<longrightarrow> g x=0)"
proof -
  have zero: "0 \<in> E" using closed unfolding division_subring_on_def by blast
  have ne: "E \<noteq> {}" using zero by blast
  let ?e = "from_nat_into E"
  let ?S = "generated_carrier_stages S0 ?e"
  let ?F = "chosen_carrier_stage_maps ?S ?e f0"
  have en: "?e n \<in> E" for n by (rule from_nat_into[OF ne])
  have erange: "range ?e=E" by (rule range_from_nat_into[OF ne count])
  have inside: "?S n \<subseteq> E" for n
  proof (rule generated_carrier_stages_inside)
    show "division_subring_on E" by (rule closed)
    show "S0 \<subseteq> E" by (rule seed)
    show "\<And>m. ?e m \<in> E" by (rule en)
  qed
  have stage_count: "countable (?S n)" for n by (rule countable_subset[OF inside count])
  have union: "(\<Union>n. ?S n)=E" by (rule generated_carrier_stages_union[OF closed seed erange])
  have choice: "dixmier_carrier_field_embedding (?S (Suc n)) (?F (Suc n)) \<and>
      (\<forall>x\<in>?S n. ?F (Suc n) x=?F n x)"
    if current: "dixmier_carrier_field_embedding (?S n) (?F n)" for n
  proof -
    have stage_closed: "division_subring_on (?S n)"
      by (rule dixmier_carrier_field_embedding.carrier_closed[OF current])
    have ex: "\<exists>G::'k \<Rightarrow> 'l. dixmier_carrier_field_embedding (division_closure (insert (?e n) (?S n))) G \<and>
        (\<forall>x\<in>?S n. G x=?F n x)"
      by (rule extend[OF inside stage_closed stage_count current en])
    have chosen: "dixmier_carrier_field_embedding (division_closure (insert (?e n) (?S n)))
        (SOME G. dixmier_carrier_field_embedding (division_closure (insert (?e n) (?S n))) G \<and>
          (\<forall>x\<in>?S n. G x=?F n x)) \<and>
      (\<forall>x\<in>?S n. (SOME G. dixmier_carrier_field_embedding (division_closure (insert (?e n) (?S n))) G \<and>
          (\<forall>x\<in>?S n. G x=?F n x)) x=?F n x)"
      by (rule someI_ex[OF ex])
    show ?thesis
      unfolding chosen_carrier_stage_maps.simps generated_carrier_stages.simps
      by (rule chosen)
  qed
  have embeddings: "dixmier_carrier_field_embedding (?S n) (?F n)" for n
  proof (induction n)
    case 0 show ?case by (simp only: generated_carrier_stages.simps chosen_carrier_stage_maps.simps initial)
  next
    case (Suc n) show ?case by (rule conjunct1[OF choice[OF Suc.IH]])
  qed
  have agreement: "?F (Suc n) x=?F n x" if "x \<in> ?S n" for n x
    by (rule bspec[OF conjunct2[OF choice[OF embeddings]] that])
  interpret chain: compatible_carrier_chain ?S ?F
  proof (rule compatible_carrier_chain.intro)
    show "?S n \<subseteq> ?S (Suc n)" for n by (rule generated_carrier_stages_increasing)
    show "dixmier_carrier_field_embedding (?S n) (?F n)" for n by (rule embeddings)
    show "x \<in> ?S n \<Longrightarrow> ?F (Suc n) x=?F n x" for n x by (rule agreement)
  qed
  let ?g = "carrier_chain_map ?S ?F"
  have result: "dixmier_carrier_field_embedding E ?g" using chain.chain_union_embedding by (simp only: union)
  have agrees: "?g x=f0 x" if "x \<in> S0" for x
  proof -
    have x0: "x \<in> ?S 0" using that by (simp only: generated_carrier_stages.simps)
    show ?thesis using chain.chain_map_on_stage[OF x0] by (simp only: chosen_carrier_stage_maps.simps)
  qed
  have outside: "?g x=0" if "x \<notin> E" for x
    by (rule chain.chain_map_outside) (simp only: union that simp_thms)
  show ?thesis
  proof (rule exI[of _ ?g], intro conjI)
    show "dixmier_carrier_field_embedding E ?g" by (rule result)
    show "\<forall>x\<in>S0. ?g x=f0 x" by (intro ballI agrees)
    show "\<forall>x. x \<notin> E \<longrightarrow> ?g x=0" by (intro allI impI outside)
  qed
qed

end
