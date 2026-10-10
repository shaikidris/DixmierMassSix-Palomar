theory Polynomial_Monomial_Shear_Recovery
 imports "Polynomial_Constant_Cut_Recovery"
   "Weyl_Statement_Interfaces"
begin

text \<open>Polynomial recovery of arbitrary nonnegative integral monomial shears.
The faithful ramified lift is used to construct the map; no polynomial-image
or polynomial-counterexample recovery assumption is introduced.\<close>

lemma monomial_lift_scalar:
 "polynomial_ramified_lift 1 (op_scalar c)=laurent_scalar c"
proof -
 have positive: "0<(1::nat)" by simp
 show ?thesis by (rule ext) (simp only: polynomial_ramified_lift_scalar[OF positive]
   normal_smult_def laurent_scalar_def id_apply)
qed

lemma monomial_scaled_atom_in_weyl:
 "(\<lambda>p. smult c (normal_monomial sigma 0 p))\<in>(weyl_algebra::complex poly_operator set)"
 unfolding weyl_algebra_def by (rule op_adjoin_smult) (rule normal_monomial_in_weyl[unfolded weyl_algebra_def])

lemma monomial_cut_shift_lift:
 "ramified_coeff_gen 1 (ramified_cut_shift 1 1 (int sigma) c)=
   polynomial_ramified_lift 1 ((\<lambda>p. smult c (normal_monomial sigma 0 p)))"
proof -
 have one: "0<(1::nat)" by simp
 have atom: "normal_monomial sigma 0\<in>(weyl_algebra::complex poly_operator set)"
   by (rule normal_monomial_in_weyl)
 have shift: "ramified_cut_shift 1 1 (int sigma) c=laurent_smult c (laurent_T (int sigma))"
   by (simp add: ramified_cut_shift_def ramified_cut_exponent_def laurent_T_def laurent_smult_single)
 have lifted: "polynomial_ramified_lift 1 (\<lambda>p. smult c (normal_monomial sigma 0 p))=
   normal_smult c (laurent_comp (ramified_coeff_mul (laurent_T (int 1*int sigma))) (ramified_derivative 1 ^^ 0))"
   by (simp only: polynomial_ramified_lift_smult[OF one atom] polynomial_ramified_lift_atom)
 show ?thesis by (rule ext)
   (simp only: lifted shift ramified_coeff_gen_def normal_smult_def ramified_coeff_mul_def
     laurent_comp_def funpow.simps(1) id_apply of_nat_1 mult_1_left;
     simp add: laurent_smult_as_multiplication mult.assoc)
qed

lemma monomial_cut_inverse_apply:
 assumes T: "T\<in>ramified_operator_algebra 1"
 shows "ramified_cut_aut 1 1 (int sigma) (-c) (ramified_cut_aut 1 1 (int sigma) c T)=T"
proof -
 have negative: "ramified_cut_shift 1 1 (int sigma) (-c) = -ramified_cut_shift 1 1 (int sigma) c"
   by (simp only: ramified_cut_shift_def Poly_Mapping.single_uminus)
 show ?thesis unfolding ramified_cut_aut_def negative
   by (rule ramified_shear_hom_inverse_left) (use T in auto)
qed

lemma polynomial_monomial_cut_has_polynomial_preimage:
 assumes P: "P\<in>(weyl_algebra::complex poly_operator set)"
 shows "\<exists>R\<in>weyl_algebra. polynomial_ramified_lift 1 R=
   ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P)"
proof -
 let ?L="polynomial_ramified_lift 1"
 let ?C="ramified_cut_aut 1 1 (int sigma) c"
 have positive: "0<(1::nat)" by simp
 have H: "ramified_alg_hom_on 1 ?C"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have x: "?C (?L x_op)=?L x_op"
   by (simp only: polynomial_ramified_lift_x ramified_cut_aut_coeff[OF positive])
 have YC: "(y_op::complex poly_operator)\<in>weyl_algebra" by (simp add: weyl_algebra_def op_adjoin.generator)
 have MC: "(\<lambda>p. smult c (normal_monomial sigma 0 p))\<in>(weyl_algebra::complex poly_operator set)"
   by (rule monomial_scaled_atom_in_weyl)
 have y: "?C (?L y_op)=?L (y_op+(\<lambda>p. smult c (normal_monomial sigma 0 p)))"
 proof -
   have "?C (?L y_op)=ramified_Y_gen 1+?L (\<lambda>p. smult c (normal_monomial sigma 0 p))"
     by (simp only: polynomial_ramified_lift_y ramified_cut_aut_Y[OF positive] monomial_cut_shift_lift)
   also have "...=?L y_op+?L (\<lambda>p. smult c (normal_monomial sigma 0 p))"
     by (simp only: polynomial_ramified_lift_y)
   also have "...=?L (y_op+(\<lambda>p. smult c (normal_monomial sigma 0 p)))"
     by (rule sym, rule polynomial_ramified_lift_add[OF positive YC MC])
   finally show ?thesis .
 qed
 show ?thesis using P unfolding weyl_algebra_def
 proof (induction rule: op_adjoin.induct)
   case (generator T)
   have alternatives: "T=x_op \<or> T=y_op" using generator.hyps by simp
   have xmember: "x_op\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.generator) simp
   have ymember: "y_op+(\<lambda>p. smult c (normal_monomial sigma 0 p))\<in>op_adjoin {x_op,y_op}"
     using YC MC unfolding weyl_algebra_def by (auto intro: op_adjoin.add)
   show ?case
   proof (cases "T=x_op")
     case True
     show ?thesis by (rule bexI[where x=x_op])
       (simp_all only: True xmember x)
   next
     case False
     have Teq: "T=y_op" using alternatives False by blast
     show ?thesis by (rule bexI[where x="y_op+(\<lambda>p. smult c (normal_monomial sigma 0 p))"])
       (simp_all only: Teq ymember y)
   qed
 next
   case (scalar z)
   have member: "op_scalar z\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.scalar)
   show ?case
     by (rule bexI[where x="op_scalar z"])
       (simp_all only: monomial_lift_scalar ramified_hom_scalar[OF H] member)
 next
   case (add T U)
   obtain R S where R: "R\<in>op_adjoin {x_op,y_op}" and S: "S\<in>op_adjoin {x_op,y_op}"
     and LR: "?L R=?C (?L T)" and LS: "?L S=?C (?L U)"
     using add.IH by blast
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using add.hyps unfolding weyl_algebra_def by blast+
   have RC: "R\<in>weyl_algebra" and SC: "S\<in>weyl_algebra"
     using R S unfolding weyl_algebra_def by blast+
   have member: "R+S\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.add[OF R S])
   show ?case by (rule bexI[of _ "R+S"])
     (simp_all only: polynomial_ramified_lift_add[OF positive RC SC]
       polynomial_ramified_lift_add[OF positive TC UC] LR LS
       ramified_hom_add[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier] member)
 next
   case (diff T U)
   obtain R S where R: "R\<in>op_adjoin {x_op,y_op}" and S: "S\<in>op_adjoin {x_op,y_op}"
     and LR: "?L R=?C (?L T)" and LS: "?L S=?C (?L U)"
     using diff.IH by blast
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using diff.hyps unfolding weyl_algebra_def by blast+
   have RC: "R\<in>weyl_algebra" and SC: "S\<in>weyl_algebra"
     using R S unfolding weyl_algebra_def by blast+
   have member: "R-S\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.diff[OF R S])
   show ?case by (rule bexI[of _ "R-S"])
     (simp_all only: polynomial_ramified_lift_diff[OF positive RC SC]
       polynomial_ramified_lift_diff[OF positive TC UC] LR LS
       ramified_hom_diff[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier] member)
 next
   case (comp T U)
   obtain R S where R: "R\<in>op_adjoin {x_op,y_op}" and S: "S\<in>op_adjoin {x_op,y_op}"
     and LR: "?L R=?C (?L T)" and LS: "?L S=?C (?L U)"
     using comp.IH by blast
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using comp.hyps unfolding weyl_algebra_def by blast+
   have RC: "R\<in>weyl_algebra" and SC: "S\<in>weyl_algebra"
     using R S unfolding weyl_algebra_def by blast+
   have member: "op_comp R S\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.comp[OF R S])
   show ?case by (rule bexI[of _ "op_comp R S"])
     (simp_all only: polynomial_ramified_lift_comp[OF positive RC SC]
       polynomial_ramified_lift_comp[OF positive TC UC] LR LS
       ramified_hom_comp[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier] member)
 qed
qed

definition monomial_polynomial_cut :: "nat \<Rightarrow> complex \<Rightarrow> complex poly_operator \<Rightarrow> complex poly_operator" where
 "monomial_polynomial_cut sigma c P=(SOME R. R\<in>weyl_algebra \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P))"

lemma monomial_polynomial_cut_spec:
 assumes P: "P\<in>weyl_algebra"
 shows "monomial_polynomial_cut sigma c P\<in>weyl_algebra \<and>
   polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c P)=
     ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P)"
 unfolding monomial_polynomial_cut_def
 by (rule someI_ex[where P="\<lambda>R. R\<in>weyl_algebra \<and> polynomial_ramified_lift 1 R=
   ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P)"])
   (use polynomial_monomial_cut_has_polynomial_preimage[where sigma=sigma and c=c, OF P] in blast)

lemma monomial_polynomial_cut_carrier:
 "P\<in>weyl_algebra \<Longrightarrow> monomial_polynomial_cut sigma c P\<in>weyl_algebra"
 using monomial_polynomial_cut_spec by blast

lemma monomial_polynomial_cut_lift:
 "P\<in>weyl_algebra \<Longrightarrow> polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c P)=
   ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P)"
 using monomial_polynomial_cut_spec by blast

lemma monomial_polynomial_cut_inverse:
 assumes P: "P\<in>weyl_algebra"
 shows "monomial_polynomial_cut sigma (-c) (monomial_polynomial_cut sigma c P)=P"
proof (rule polynomial_ramified_lift_injective[where l=1])
 show "0<(1::nat)" by simp
 show "monomial_polynomial_cut sigma (-c) (monomial_polynomial_cut sigma c P)\<in>weyl_algebra"
   by (intro monomial_polynomial_cut_carrier P)
 show "P\<in>weyl_algebra" by (rule P)
 show "polynomial_ramified_lift 1 (monomial_polynomial_cut sigma (-c) (monomial_polynomial_cut sigma c P))=
   polynomial_ramified_lift 1 P"
   by (simp only: monomial_polynomial_cut_lift[OF monomial_polynomial_cut_carrier[OF P]]
     monomial_polynomial_cut_lift[OF P]
     monomial_cut_inverse_apply[OF polynomial_ramified_lift_carrier])
qed

lemma monomial_polynomial_cut_scalar:
 "monomial_polynomial_cut sigma c (op_scalar z)=op_scalar z"
proof (rule polynomial_ramified_lift_injective[where l=1])
 show "0<(1::nat)" by simp
 show "monomial_polynomial_cut sigma c (op_scalar z)\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier) (simp add: weyl_algebra_def op_adjoin.scalar)
 show "op_scalar z\<in>(weyl_algebra::complex poly_operator set)"
   by (simp add: weyl_algebra_def op_adjoin.scalar)
 show "polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c (op_scalar z))=
   polynomial_ramified_lift 1 (op_scalar z)"
 proof -
   have scalar_carrier: "op_scalar z\<in>(weyl_algebra::complex poly_operator set)"
     by (simp add: weyl_algebra_def op_adjoin.scalar)
   have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 (int sigma) c)"
     by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
   show ?thesis by (simp only: monomial_polynomial_cut_lift[OF scalar_carrier]
     monomial_lift_scalar ramified_hom_scalar[OF H])
 qed
qed

lemma monomial_polynomial_cut_add:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "monomial_polynomial_cut sigma c (P+Q)=monomial_polynomial_cut sigma c P+monomial_polynomial_cut sigma c Q"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "monomial_polynomial_cut sigma c P\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF P])
 have EQ: "monomial_polynomial_cut sigma c Q\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF Q])
 have source: "P+Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "monomial_polynomial_cut sigma c P+monomial_polynomial_cut sigma c Q\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "monomial_polynomial_cut sigma c (P+Q)\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 (int sigma) c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c (P+Q))=
   polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c P+monomial_polynomial_cut sigma c Q)"
   by (simp only: monomial_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_add[OF positive P Q]
     polynomial_ramified_lift_add[OF positive EP EQ]
     monomial_polynomial_cut_lift[OF P] monomial_polynomial_cut_lift[OF Q]
     ramified_hom_add[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma monomial_polynomial_cut_diff:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "monomial_polynomial_cut sigma c (P-Q)=monomial_polynomial_cut sigma c P-monomial_polynomial_cut sigma c Q"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "monomial_polynomial_cut sigma c P\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF P])
 have EQ: "monomial_polynomial_cut sigma c Q\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF Q])
 have source: "P-Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "monomial_polynomial_cut sigma c P-monomial_polynomial_cut sigma c Q\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "monomial_polynomial_cut sigma c (P-Q)\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 (int sigma) c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c (P-Q))=
   polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c P-monomial_polynomial_cut sigma c Q)"
   by (simp only: monomial_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_diff[OF positive P Q]
     polynomial_ramified_lift_diff[OF positive EP EQ]
     monomial_polynomial_cut_lift[OF P] monomial_polynomial_cut_lift[OF Q]
     ramified_hom_diff[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma monomial_polynomial_cut_comp:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "monomial_polynomial_cut sigma c (op_comp P Q)=op_comp (monomial_polynomial_cut sigma c P) (monomial_polynomial_cut sigma c Q)"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "monomial_polynomial_cut sigma c P\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF P])
 have EQ: "monomial_polynomial_cut sigma c Q\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF Q])
 have source: "op_comp P Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "op_comp (monomial_polynomial_cut sigma c P) (monomial_polynomial_cut sigma c Q)\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "monomial_polynomial_cut sigma c (op_comp P Q)\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 (int sigma) c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (monomial_polynomial_cut sigma c (op_comp P Q))=
   polynomial_ramified_lift 1 (op_comp (monomial_polynomial_cut sigma c P) (monomial_polynomial_cut sigma c Q))"
   by (simp only: monomial_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_comp[OF positive P Q]
     polynomial_ramified_lift_comp[OF positive EP EQ]
     monomial_polynomial_cut_lift[OF P] monomial_polynomial_cut_lift[OF Q]
     ramified_hom_comp[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma monomial_polynomial_cut_id:
 "monomial_polynomial_cut sigma c id=id"
proof -
 have scalar: "(op_scalar 1::complex poly_operator)=id"
   by (rule ext) (simp add: op_scalar_def)
 show ?thesis using monomial_polynomial_cut_scalar[where sigma=sigma and c=c and z=1] by (simp only: scalar)
qed

lemma monomial_polynomial_cut_hom:
 "polynomial_alg_hom_on (monomial_polynomial_cut sigma c)"
 by (auto simp only: polynomial_alg_hom_on_def intro: monomial_polynomial_cut_carrier
   monomial_polynomial_cut_scalar monomial_polynomial_cut_add
   monomial_polynomial_cut_diff monomial_polynomial_cut_comp)

lemma polynomial_monomial_cut_has_polynomial_automorphism:
 "\<exists>E H. polynomial_alg_aut_on E H \<and> (\<forall>P\<in>weyl_algebra.
   polynomial_ramified_lift 1 (E P)=
     ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P))"
proof -
 have aut: "polynomial_alg_aut_on (monomial_polynomial_cut sigma c) (monomial_polynomial_cut sigma (-c))"
   unfolding polynomial_alg_aut_on_def
   using monomial_polynomial_cut_hom[where sigma=sigma and c=c] monomial_polynomial_cut_hom[where sigma=sigma and c="-c"]
     monomial_polynomial_cut_inverse[where sigma=sigma and c=c] monomial_polynomial_cut_inverse[where sigma=sigma and c="-c"]
   by auto
 show ?thesis by (intro exI[of _ "monomial_polynomial_cut sigma c"]
     exI[of _ "monomial_polynomial_cut sigma (-c)"])
   (use aut monomial_polynomial_cut_lift in blast)
qed

lemma monomial_polynomial_cut_adjoin_image:
 assumes generators: "G\<subseteq>(weyl_algebra::complex poly_operator set)"
 and member: "T\<in>op_adjoin G"
 shows "monomial_polynomial_cut sigma c T\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
proof -
 from member have "T\<in>weyl_algebra \<and>
   monomial_polynomial_cut sigma c T\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
 proof (induction rule: op_adjoin.induct)
   case (generator T)
   then show ?case using generators by (auto intro: op_adjoin.generator)
 next
   case (scalar z)
   then show ?case by (simp add: monomial_polynomial_cut_scalar weyl_algebra_def op_adjoin.scalar)
 next
   case (add T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using add.IH by blast+
   have source_closed: "T+U\<in>weyl_algebra"
     using weyl_subalgebra TC UC unfolding op_subalgebra_def by blast
   have target_closed: "monomial_polynomial_cut sigma c T+monomial_polynomial_cut sigma c U\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     by (rule op_adjoin.add) (use add.IH in blast)+
   have result: "T+U\<in>weyl_algebra \<and>
     monomial_polynomial_cut sigma c (T+U)\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     using source_closed target_closed by (simp only: monomial_polynomial_cut_add[OF TC UC]; blast)
   show ?case using result by (simp only: plus_fun_def)
 next
   case (diff T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using diff.IH by blast+
   have source_closed: "T-U\<in>weyl_algebra"
     using weyl_subalgebra TC UC unfolding op_subalgebra_def by blast
   have target_closed: "monomial_polynomial_cut sigma c T-monomial_polynomial_cut sigma c U\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     by (rule op_adjoin.diff) (use diff.IH in blast)+
   have result: "T-U\<in>weyl_algebra \<and>
     monomial_polynomial_cut sigma c (T-U)\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     using source_closed target_closed by (simp only: monomial_polynomial_cut_diff[OF TC UC]; blast)
   have representation: "(\<lambda>a. T a-U a)=T-U" by (rule ext) (simp only: minus_apply)
   show ?case using result by (simp only: representation)
 next
   case (comp T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using comp.IH by blast+
   have source_closed: "op_comp T U\<in>weyl_algebra"
     using weyl_subalgebra TC UC unfolding op_subalgebra_def by blast
   have target_closed: "op_comp (monomial_polynomial_cut sigma c T) (monomial_polynomial_cut sigma c U)\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     by (rule op_adjoin.comp) (use comp.IH in blast)+
   have result: "op_comp T U\<in>weyl_algebra \<and>
     monomial_polynomial_cut sigma c (op_comp T U)\<in>op_adjoin (monomial_polynomial_cut sigma c ` G)"
     using source_closed target_closed by (simp only: monomial_polynomial_cut_comp[OF TC UC]; blast)
   show ?case by (fact result)
 qed
 then show ?thesis by blast
qed

lemma polynomial_monomial_cut_recovers_polynomial_counterexample:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "\<exists>R S. is_counterexample_pair R S \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P) \<and>
   polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 Q)"
proof -
 let ?R="monomial_polynomial_cut sigma c P"
 let ?S="monomial_polynomial_cut sigma c Q"
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   using pair unfolding is_counterexample_pair_def by blast+
 have R: "?R\<in>weyl_algebra" and S: "?S\<in>weyl_algebra"
   by (rule monomial_polynomial_cut_carrier[OF P], rule monomial_polynomial_cut_carrier[OF Q])
 have exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast
 have QP: "op_comp Q P\<in>weyl_algebra" and PQ: "op_comp P Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast+
 have image_exact: "op_comp ?S ?R-op_comp ?R ?S=id"
   using arg_cong[OF exact, of "monomial_polynomial_cut sigma c"]
   by (simp only: monomial_polynomial_cut_diff[OF QP PQ]
      monomial_polynomial_cut_comp[OF Q P] monomial_polynomial_cut_comp[OF P Q]
      monomial_polynomial_cut_id)
 have nongeneration: "op_adjoin {?R,?S}\<noteq>weyl_algebra"
 proof
   assume generation: "op_adjoin {?R,?S}=weyl_algebra"
   have reverse: "weyl_algebra\<subseteq>op_adjoin {P,Q}"
   proof
     fix T::"complex poly_operator" assume T: "T\<in>weyl_algebra"
     have ET: "monomial_polynomial_cut sigma c T\<in>op_adjoin {?R,?S}"
       using monomial_polynomial_cut_carrier[OF T] generation by simp
     have generators: "{?R,?S}\<subseteq>weyl_algebra" using R S by auto
     have recovered: "monomial_polynomial_cut sigma (-c) (monomial_polynomial_cut sigma c T)
       \<in>op_adjoin (monomial_polynomial_cut sigma (-c) ` {?R,?S})"
       by (rule monomial_polynomial_cut_adjoin_image[OF generators ET])
     show "T\<in>op_adjoin {P,Q}" using recovered
       by (simp only: monomial_polynomial_cut_inverse[OF T]
         image_insert image_empty monomial_polynomial_cut_inverse[OF P]
         monomial_polynomial_cut_inverse[OF Q])
   qed
   have forward: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
     by (rule pair_generated_inside_weyl[OF P Q])
   have "op_adjoin {P,Q}=weyl_algebra" using forward reverse by blast
   then show False using pair unfolding is_counterexample_pair_def by blast
 qed
 have actual_pair: "is_counterexample_pair ?R ?S"
   using R S image_exact nongeneration unfolding is_counterexample_pair_def by blast
 show ?thesis by (intro exI[of _ ?R] exI[of _ ?S])
   (use actual_pair monomial_polynomial_cut_lift[OF P]
      monomial_polynomial_cut_lift[OF Q] in blast)
qed

end
