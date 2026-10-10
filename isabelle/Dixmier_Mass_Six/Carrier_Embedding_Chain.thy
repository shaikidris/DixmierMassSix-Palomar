theory Carrier_Embedding_Chain
 imports "Carrier_Field_Embedding"
begin
definition carrier_chain_map :: "(nat\<Rightarrow>'k set)\<Rightarrow>(nat\<Rightarrow>'k\<Rightarrow>'l::zero)\<Rightarrow>'k\<Rightarrow>'l" where
 "carrier_chain_map S F x=(if x\<in>(\<Union>n. S n) then F(LEAST n. x\<in>S n)x else 0)"
locale compatible_carrier_chain =
 fixes S :: "nat\<Rightarrow>'k::field set" and F :: "nat\<Rightarrow>'k\<Rightarrow>'l::field"
 assumes increasing: "S n\<subseteq>S(Suc n)"
 and embeddings: "dixmier_carrier_field_embedding (S n) (F n)"
 and successor_agreement: "x\<in>S n \<Longrightarrow> F(Suc n)x=F n x"
begin
lemma chain_nested: "n\<le>m \<Longrightarrow> S n\<subseteq>S m"
 by (rule lift_Suc_mono_le[where f=S, OF increasing])
lemma chain_agreement:
 assumes le: "n\<le>m" and xn: "x\<in>S n"
 shows "F m x=F n x"
 using le xn
proof (induction m arbitrary: n)
 case 0 then show ?case by simp
next
 case (Suc m)
 show ?case
 proof (cases "n=Suc m")
  case True then show ?thesis by simp
 next
  case False
  have nm: "n\<le>m" using Suc.prems(1) False by arith
  have xm: "x\<in>S m" using chain_nested[OF nm] Suc.prems(2) by auto
  show ?thesis using successor_agreement[OF xm] Suc.IH[OF nm Suc.prems(2)] by simp
 qed
qed
lemma chain_map_on_stage:
 assumes xn: "x\<in>S n"
 shows "carrier_chain_map S F x=F n x"
proof -
 have member: "x\<in>(\<Union>n. S n)" using xn by auto
 have least: "x\<in>S(LEAST m. x\<in>S m)" by (rule LeastI_ex) (use xn in auto)
 have le: "(LEAST m. x\<in>S m)\<le>n" by (rule Least_le[where P="\<lambda>m. x\<in>S m" and k=n, OF xn])
 show ?thesis unfolding carrier_chain_map_def using member chain_agreement[OF le least] by simp
qed
lemma stage_zero: "0\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_zero[OF embeddings])
lemma stage_one: "1\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_one[OF embeddings])
lemma stage_neg: "x\<in>S n \<Longrightarrow> -x\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_neg[OF embeddings])
lemma stage_inverse: "x\<in>S n \<Longrightarrow> inverse x\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_inverse[OF embeddings])
lemma stage_add: "x\<in>S n \<Longrightarrow> y\<in>S n \<Longrightarrow> x+y\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_add[OF embeddings])
lemma stage_mult: "x\<in>S n \<Longrightarrow> y\<in>S n \<Longrightarrow> x*y\<in>S n"
 by (rule dixmier_carrier_field_embedding.E_mult[OF embeddings])
lemma chain_common_stage:
 assumes xu: "x\<in>(\<Union>n. S n)" and yu: "y\<in>(\<Union>n. S n)"
 obtains n where "x\<in>S n" "y\<in>S n"
proof -
 obtain i where xi: "x\<in>S i" using xu by auto
 obtain j where yj: "y\<in>S j" using yu by auto
 have x: "x\<in>S(max i j)" using xi chain_nested[of i "max i j"] by auto
 have y: "y\<in>S(max i j)" using yj chain_nested[of j "max i j"] by auto
 show thesis by (rule that[OF x y])
qed
lemma chain_union_closed: "division_subring_on (\<Union>n. S n)"
proof -
 let ?U="\<Union>n. S n"
 have zero: "0\<in>?U" and one: "1\<in>?U" using stage_zero[of 0] stage_one[of 0] by auto
 have neg: "-x\<in>?U" if xu: "x\<in>?U" for x
 proof -
  obtain n where xn: "x\<in>S n" using xu by auto
  show ?thesis using stage_neg[OF xn] by auto
 qed
 have inv: "inverse x\<in>?U" if xu: "x\<in>?U" for x
 proof -
  obtain n where xn: "x\<in>S n" using xu by auto
  show ?thesis using stage_inverse[OF xn] by auto
 qed
 have ops: "x+y\<in>?U \<and> x*y\<in>?U" if xu: "x\<in>?U" and yu: "y\<in>?U" for x y
 proof -
  obtain n where xn: "x\<in>S n" and yn: "y\<in>S n" by (rule chain_common_stage[OF xu yu])
  show ?thesis using stage_add[OF xn yn] stage_mult[OF xn yn] by auto
 qed
 show ?thesis unfolding division_subring_on_def
 proof (intro conjI)
  show "0\<in>?U" by fact
  show "1\<in>?U" by fact
  show "\<forall>x\<in>?U. -x\<in>?U" by (intro ballI; rule neg; assumption)
  show "\<forall>x\<in>?U. inverse x\<in>?U" by (intro ballI; rule inv; assumption)
  show "\<forall>x\<in>?U. \<forall>y\<in>?U. x+y\<in>?U \<and> x*y\<in>?U" by (intro ballI; rule ops; assumption+)
 qed
qed
lemma chain_union_embedding:
 "dixmier_carrier_field_embedding (\<Union>n. S n) (carrier_chain_map S F)"
proof
 show "division_subring_on (\<Union>n. S n)" by (rule chain_union_closed)
 show "carrier_chain_map S F 1=1" using chain_map_on_stage[OF stage_one[of 0]] dixmier_carrier_field_embedding.map_one[OF embeddings[of 0]] by simp
next
 fix x y assume xu: "x\<in>(\<Union>n. S n)" and yu: "y\<in>(\<Union>n. S n)"
 obtain n where xn: "x\<in>S n" and yn: "y\<in>S n" by (rule chain_common_stage[OF xu yu])
 show "carrier_chain_map S F (x+y)=carrier_chain_map S F x+carrier_chain_map S F y"
  by (simp only: chain_map_on_stage[OF stage_add[OF xn yn]] chain_map_on_stage[OF xn] chain_map_on_stage[OF yn] dixmier_carrier_field_embedding.map_add_on[OF embeddings xn yn])
next
 fix x y assume xu: "x\<in>(\<Union>n. S n)" and yu: "y\<in>(\<Union>n. S n)"
 obtain n where xn: "x\<in>S n" and yn: "y\<in>S n" by (rule chain_common_stage[OF xu yu])
 show "carrier_chain_map S F (x*y)=carrier_chain_map S F x*carrier_chain_map S F y"
  by (simp only: chain_map_on_stage[OF stage_mult[OF xn yn]] chain_map_on_stage[OF xn] chain_map_on_stage[OF yn] dixmier_carrier_field_embedding.map_mult_on[OF embeddings xn yn])
next
 show "inj_on (carrier_chain_map S F) (\<Union>n. S n)"
 proof (rule inj_onI)
  fix x y assume xu: "x\<in>(\<Union>n. S n)" and yu: "y\<in>(\<Union>n. S n)" and eq: "carrier_chain_map S F x=carrier_chain_map S F y"
  obtain n where xn: "x\<in>S n" and yn: "y\<in>S n" by (rule chain_common_stage[OF xu yu])
  have e: "F n x=F n y" using eq by (simp only: chain_map_on_stage[OF xn] chain_map_on_stage[OF yn])
  show "x=y" by (rule inj_onD[OF dixmier_carrier_field_embedding.injective_on[OF embeddings] e xn yn])
 qed
qed
lemma chain_map_outside:
 "x\<notin>(\<Union>n. S n) \<Longrightarrow> carrier_chain_map S F x=0"
 by (simp add: carrier_chain_map_def)
end
end
