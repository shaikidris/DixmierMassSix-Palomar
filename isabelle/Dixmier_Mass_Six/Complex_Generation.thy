theory Complex_Generation
 imports "Negative_Crossing"
   "Horizontal_Crossing"
   "Two_Root_Mass_Six"
   "Fourier_Generation"
begin

declare id_def [simp del]

lemma caseAlternative_contradiction:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
 and mass: "weyl_mass P\<le>6" and alternative: "case_alternative P"
 shows False
proof -
 have cases: "(\<exists>rho sigma::int. 0<rho \<and> -rho<sigma \<and> sigma\<le>0 \<and>
 gcd(nat(abs rho))(nat(abs sigma))=1 \<and> strict_crossing rho sigma P) \<or>
 10\<le>weyl_mass P \<or> two_root_total_symbol P"
  using alternative unfolding case_alternative_def by blast
 then show False
 proof (elim disjE)
  assume "\<exists>rho sigma::int. 0<rho \<and> -rho<sigma \<and> sigma\<le>0 \<and>
   gcd(nat(abs rho))(nat(abs sigma))=1 \<and> strict_crossing rho sigma P"
  then obtain rho sigma::int where rho: "0<rho" and lower: "-rho<sigma" and upper: "sigma\<le>0"
   and primitive: "gcd(nat(abs rho))(nat(abs sigma))=1" and crossing: "strict_crossing rho sigma P" by (elim exE conjE) assumption
  show False
  proof (cases "sigma=0")
   case True
   have rho1: "rho=1" using primitive rho True by simp
   have "strict_crossing 1 0 P" using crossing True rho1 by simp
   then show False using horizontalCrossingExclusion_of_GGV[OF inputs pair mass] by blast
  next
   case False
   define r::nat where "r=nat rho"
   define s::nat where "s=nat(-sigma)"
   have r: "int r=rho" using rho by (simp add: r_def)
   have s: "int s=-sigma" using upper by (simp add: s_def)
   have spos: "1\<le>s" using s upper False by arith
   have direction: "s<r" using r s lower by arith
   have abs_rho: "abs rho=rho" using rho by simp
   have abs_sigma: "abs sigma=-sigma" using upper by simp
   have gcd_rs: "gcd r s=1"
    using primitive by (simp only: abs_rho abs_sigma r_def s_def)
   have coprime: "coprime r s" by (simp only: coprime_iff_gcd_eq_1 gcd_rs)
   have crossing': "strict_crossing(int r)(-int s)P" using crossing r s by simp
   show False using negativeCrossingExclusion_of_GGV[OF inputs pair mass spos direction coprime] crossing' by blast
  qed
 next
  assume "10\<le>weyl_mass P"
  then show False using mass by arith
 next
  assume two: "two_root_total_symbol P"
  show False by (rule twoRoot_massSix_contradiction_of_GGV[OF inputs pair mass two])
 qed
qed

lemma massSixGeneration_complex_of_GGV:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and comm: "op_comp Q P-op_comp P Q=id" and mass: "weyl_mass P\<le>6"
 shows "op_adjoin {P,Q}=weyl_algebra"
proof (rule ccontr)
 assume non: "op_adjoin {P,Q}\<noteq>weyl_algebra"
 have pair: "is_counterexample_pair P Q" using P Q comm non unfolding is_counterexample_pair_def by blast
 have cases: "case_alternative P \<or> case_alternative(fourier_alg_hom P)"
  using inputs pair unfolding GGVInputs_def GGVCaseSplitInput_def by blast
 then show False
 proof
  assume "case_alternative P"
  then show False by (rule caseAlternative_contradiction[OF inputs pair mass])
 next
  assume alternative: "case_alternative(fourier_alg_hom P)"
  have pairF: "is_counterexample_pair(fourier_alg_hom P)(fourier_alg_hom Q)"
   by (rule isCounterexamplePair_fourier[OF pair])
  have massF: "weyl_mass(fourier_alg_hom P)\<le>6" using mass mass_fourierAlgHom[OF P] by simp
  show False by (rule caseAlternative_contradiction[OF inputs pairF massF alternative])
 qed
qed

end
