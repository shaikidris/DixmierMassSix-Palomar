theory Carrier_Weyl_Span_Descent
  imports Carrier_PBW_Transport
begin

context dixmier_carrier_char_zero_embedding
begin

theorem carrier_finite_weyl_span_descends:
  fixes J :: "'j set" and v :: "'j \<Rightarrow> 'k poly_operator" and T :: "'k poly_operator"
  assumes finite_J: "finite J"
    and vectors: "\<And>j. j \<in> J \<Longrightarrow> v j \<in> carrier_weyl E"
    and target: "T \<in> carrier_weyl E"
    and solution: "\<exists>x :: 'j \<Rightarrow> 'l.
      (\<Sum>j\<in>J. (\<lambda>p. smult (x j) (concrete_base_change f (v j) p))) = concrete_base_change f T"
  shows "\<exists>y :: 'j \<Rightarrow> 'k. (\<forall>j. y j \<in> E) \<and>
    (\<Sum>j\<in>J. (\<lambda>p. smult (y j) (v j p))) = T"
proof -
  obtain x where equality:
    "(\<Sum>j\<in>J. (\<lambda>p. smult (x j) (concrete_base_change f (v j) p))) = concrete_base_change f T"
    using solution by blast
  have vw: "v j \<in> weyl_algebra" if "j \<in> J" for j
    by (rule carrier_weyl_in_weyl[OF vectors[OF that]])
  have tw: "T \<in> weyl_algebra" by (rule carrier_weyl_in_weyl[OF target])
  let ?A = "\<lambda>u j. pbw_coeff (v j) (fst u) (snd u)"
  let ?b = "\<lambda>u. pbw_coeff T (fst u) (snd u)"
  have coordinates: "(\<Sum>j\<in>J. f (?A u j)*x j) = f (?b u)" for u
    using arg_cong[OF equality, of "\<lambda>V. pbw_coeff V (fst u) (snd u)"]
    by (simp add: bc_pbw_coeff_sum pbw_coeff_smult
        carrier_base_change_coeff[OF vw] carrier_base_change_coeff[OF tw] mult.commute)
  have ex: "\<exists>y::'j \<Rightarrow> 'k. (\<forall>j. y j \<in> E) \<and>
    (\<forall>u\<in>(UNIV::(nat\<times>nat) set). (\<Sum>j\<in>J. ?A u j*y j) = ?b u)"
  proof (rule carrier_finite_system_solution[OF finite_J, where x=x])
    show "\<And>u j. u \<in> (UNIV::(nat\<times>nat) set) \<Longrightarrow> j \<in> J \<Longrightarrow> ?A u j \<in> E"
      by (intro carrier_weyl_coeff vectors)
    show "\<And>u. u \<in> (UNIV::(nat\<times>nat) set) \<Longrightarrow> ?b u \<in> E"
      by (rule carrier_weyl_coeff[OF target])
    show "\<And>u. u \<in> (UNIV::(nat\<times>nat) set) \<Longrightarrow>
      (\<Sum>j\<in>J. f (?A u j)*x j) = f (?b u)" by (rule coordinates)
  qed
  then obtain y where ye: "\<forall>j. y j \<in> E"
    and ys: "\<forall>u\<in>(UNIV::(nat\<times>nat) set). (\<Sum>j\<in>J. ?A u j*y j) = ?b u" by blast
  let ?S = "\<Sum>j\<in>J. (\<lambda>p. smult (y j) (v j p))"
  have sw: "?S \<in> weyl_algebra" by (intro bc_weyl_sum bc_weyl_smult vw)
  have st: "?S=T"
  proof (rule weyl_pbw_injective[OF sw tw])
    fix a b
    have "(\<Sum>j\<in>J. pbw_coeff (v j) a b*y j) = pbw_coeff T a b"
      using ys[rule_format, of "(a,b)"] by simp
    then show "pbw_coeff ?S a b = pbw_coeff T a b"
      by (simp add: bc_pbw_coeff_sum pbw_coeff_smult mult.commute)
  qed
  show ?thesis by (rule exI[of _ y]) (simp only: ye st simp_thms)
qed

end
end
