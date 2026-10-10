theory Root_Multiplicity_Adapter
  imports "HOL-Computational_Algebra.Polynomial"
begin

definition rootMultiplicity :: "complex \<Rightarrow> complex poly \<Rightarrow> nat" where
  "rootMultiplicity a p = (if p=0 then 0 else Polynomial.order a p)"

lemma rootMultiplicity_zero [simp]: "rootMultiplicity a 0 = 0"
  by (simp add: rootMultiplicity_def)

lemma rootMultiplicity_eq_order:
  "p \<noteq> 0 \<Longrightarrow> rootMultiplicity a p = Polynomial.order a p"
  by (simp add: rootMultiplicity_def)

lemma rootMultiplicity_eq_count_proots:
  "rootMultiplicity a p = count (proots p) a"
  by (cases "p=0") (simp_all add: rootMultiplicity_def)

end
