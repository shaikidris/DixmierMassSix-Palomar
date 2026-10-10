theory Pure_Grade_Commutator
 imports "Poisson_Endpoint_Maximizers"
   "Face_Mass_Geometry"
begin

lemma pure_total_leading_nonzero:
 fixes T :: "complex poly_operator"
 assumes carrier: "T\<in>weyl_algebra" and nonzero: "T\<noteq>0"
 shows "leading_form 1 1 T\<noteq>0"
proof -
 have symbol: "pbw_symbol T\<noteq>0"
 proof
  assume zero: "pbw_symbol T=0"
  have "T=0" by (rule weyl_symbol_injective[OF carrier _])
    (use zero in \<open>simp_all add: weyl_algebra_def\<close>)
  then show False using nonzero by contradiction
 qed
 have degree: "weighted_degree 1 1 (pbw_symbol T)=bot.Value (v_degree 1 1 T)"
   using symbol by (cases "weighted_degree 1 1 (pbw_symbol T)")
     (simp_all add: v_degree_def)
 show ?thesis unfolding leading_form_def by (rule weighted_top_component_nonzero[OF degree])
qed

lemma pure_total_leading_monomial:
 fixes T :: "complex poly_operator"
 assumes carrier: "T\<in>weyl_algebra" and nonzero: "T\<noteq>0"
   and grade: "\<And>u. u\<in>biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u=j"
 shows "\<exists>d a. leading_form 1 1 T=biv_monom a (fst d) (snd d) \<and> a\<noteq>0 \<and> pair_grade d=j"
proof -
 let ?F="leading_form 1 1 T"
 have nonzero_face: "?F\<noteq>0" by (rule pure_total_leading_nonzero[OF carrier nonzero])
 have nonempty: "biv_support ?F\<noteq>{}" using nonzero_face by simp
 obtain d where d: "d\<in>biv_support ?F" using nonempty by blast
 have hom: "weighted_homogeneous 1 1 (v_degree 1 1 T) ?F"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have injective: "inj_on pair_grade (biv_support ?F)"
   by (rule grade_injective_on_homogeneous_face[OF _ hom]) simp
 have full: "d\<in>biv_support (pbw_symbol T)"
   using d weighted_component_support_subset[of 1 1 "v_degree 1 1 T" "pbw_symbol T"]
   by (simp only: leading_form_def; blast)
 have dg: "pair_grade d=j" by (rule grade[OF full])
 have unique: "u=d" if "u\<in>biv_support ?F" for u
 proof -
  have ug: "pair_grade u=j"
    by (rule grade) (use that weighted_component_support_subset[of 1 1 "v_degree 1 1 T" "pbw_symbol T"] in \<open>simp only: leading_form_def; blast\<close>)
  show ?thesis by (rule inj_onD[OF injective _ that d]) (simp only: ug dg)
 qed
 have representation: "?F=biv_monom (biv_coeff ?F (fst d) (snd d)) (fst d) (snd d)"
 proof (rule biv_eqI)
  fix i k
  show "biv_coeff ?F i k=biv_coeff (biv_monom (biv_coeff ?F (fst d) (snd d)) (fst d) (snd d)) i k"
  proof (cases "(i,k)=d")
   case True then show ?thesis by (cases d) simp
  next
   case False
   have "(i,k)\<notin>biv_support ?F" using unique False by blast
   then have "biv_coeff ?F i k=0" by (simp add: biv_support_def)
   then show ?thesis using False by (auto simp: prod_eq_iff)
  qed
 qed
 have coefficient: "biv_coeff ?F (fst d) (snd d)\<noteq>0" using d by (simp add: biv_support_def)
 show ?thesis using representation coefficient dg by blast
qed

lemma pureGrade_minusOne_positive_commutator_ne_zero:
 fixes P Q :: "complex poly_operator" and j :: nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and positive: "0<j" and pnz: "P\<noteq>0" and qnz: "Q\<noteq>0"
   and pg: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u=-1"
   and qg: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u=int j"
 shows "op_comp Q P-op_comp P Q\<noteq>0"
proof -
 obtain d a where df: "leading_form 1 1 Q=biv_monom a (fst d) (snd d)"
   and an: "a\<noteq>0" and dg: "pair_grade d=int j"
   using pure_total_leading_monomial[OF Q qnz qg] by blast
 obtain e b where ef: "leading_form 1 1 P=biv_monom b (fst e) (snd e)"
   and bn: "b\<noteq>0" and eg: "pair_grade e=-1"
   using pure_total_leading_monomial[OF P pnz pg] by blast
 have dc: "fst d=snd d+j" using dg by (simp add: pair_grade_def; arith)
 have ec: "snd e=fst e+1" using eg by (simp add: pair_grade_def; arith)
 have positive_product: "0<j*(fst e+1)" by (rule mult_pos_pos[OF positive]) simp
 have positive_sum: "0<snd d+j*(fst e+1)" using positive_product by arith
 have cast_nonzero: "(of_nat (snd d+j*(fst e+1))::complex)\<noteq>0"
   using positive_sum by (simp only: of_nat_eq_0_iff; arith)
 have determinant: "(of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e)=
   -of_nat (snd d+j*(fst e+1))"
   by (simp add: dc ec algebra_simps)
 have coefficient_nonzero: "((of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e))*(a*b)\<noteq>0"
   using cast_nonzero an bn by (simp only: determinant mult_eq_0_iff neg_equal_0_iff_equal; blast)
 have bracket: "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)\<noteq>0"
 proof
  assume zero: "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)=0"
  have coefficient_zero: "((of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e))*(a*b)=0"
   using arg_cong[OF zero, of "\<lambda>F. biv_coeff F (fst d+fst e-1) (snd d+snd e-1)"]
   by (simp only: df ef poisson_monomial_general endpoint_biv_smult_monom; simp)
  show False using coefficient_zero coefficient_nonzero by contradiction
 qed
 show ?thesis
 proof
  assume zero: "op_comp Q P-op_comp P Q=0"
  have top: "leading_form 1 1 (op_comp Q P-op_comp P Q)=
    biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)"
    using leading_form_commutator[OF P Q _ bracket] by auto
  have "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)=0" using top zero
    by (simp add: leading_form_def)
  then show False using bracket by contradiction
 qed
qed
end
