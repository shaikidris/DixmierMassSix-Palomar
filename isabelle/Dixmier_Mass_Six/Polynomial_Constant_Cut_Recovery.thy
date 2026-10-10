theory Polynomial_Constant_Cut_Recovery
 imports "Polynomial_Ramified_Lift_Homomorphism"
   "Weyl_Statement_Interfaces"
begin

text \<open>Ordinary polynomial recovery of the actual horizontal constant cut.
The faithful ramified lift is used to construct the map; no polynomial-image
or polynomial-counterexample recovery assumption is introduced.\<close>

lemma horizontal_lift_scalar:
 "polynomial_ramified_lift 1 (op_scalar c)=laurent_scalar c"
proof -
 have positive: "0<(1::nat)" by simp
 show ?thesis by (rule ext) (simp only: polynomial_ramified_lift_scalar[OF positive]
   normal_smult_def laurent_scalar_def id_apply)
qed

lemma horizontal_cut_shift_scalar:
 "ramified_coeff_gen 1 (ramified_cut_shift 1 1 0 c)=laurent_scalar c"
 by (simp add: ramified_cut_shift_def ramified_cut_exponent_def
   ramified_coeff_gen_def ramified_coeff_mul_C)

lemma horizontal_cut_inverse_apply:
 assumes T: "T\<in>ramified_operator_algebra 1"
 shows "ramified_cut_aut 1 1 0 (-c) (ramified_cut_aut 1 1 0 c T)=T"
proof -
 have negative: "ramified_cut_shift 1 1 0 (-c) = -ramified_cut_shift 1 1 0 c"
   by (simp add: ramified_cut_shift_def Poly_Mapping.single_uminus)
 show ?thesis unfolding ramified_cut_aut_def negative
   by (rule ramified_shear_hom_inverse_left) (use T in auto)
qed

lemma horizontal_cut_has_polynomial_preimage:
 assumes P: "P\<in>(weyl_algebra::complex poly_operator set)"
 shows "\<exists>R\<in>weyl_algebra. polynomial_ramified_lift 1 R=
   ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"
proof -
 let ?L="polynomial_ramified_lift 1"
 let ?C="ramified_cut_aut 1 1 0 c"
 have positive: "0<(1::nat)" by simp
 have H: "ramified_alg_hom_on 1 ?C"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have x: "?C (?L x_op)=?L x_op"
   by (simp only: polynomial_ramified_lift_x ramified_cut_aut_coeff[OF positive])
 have yc: "y_op\<in>(weyl_algebra::complex poly_operator set)"
   unfolding weyl_algebra_def by (rule op_adjoin.generator) simp
 have sc: "op_scalar c\<in>(weyl_algebra::complex poly_operator set)"
   unfolding weyl_algebra_def by (rule op_adjoin.scalar)
 have lift_sum: "?L(y_op+op_scalar c)=?L y_op+?L(op_scalar c)"
   by (rule polynomial_ramified_lift_add[OF positive yc sc])
 have y: "?C (?L y_op)=?L (y_op+op_scalar c)"
   by (simp only: lift_sum polynomial_ramified_lift_y ramified_cut_aut_Y[OF positive]
     horizontal_cut_shift_scalar horizontal_lift_scalar)
 show ?thesis using P unfolding weyl_algebra_def
 proof (induction rule: op_adjoin.induct)
   case (generator T)
   have alternatives: "T=x_op \<or> T=y_op" using generator.hyps by simp
   have xmember: "x_op\<in>op_adjoin {x_op,y_op}" by (rule op_adjoin.generator) simp
   have ymember: "y_op+op_scalar c\<in>op_adjoin {x_op,y_op}"
     by (rule op_adjoin.add) (rule op_adjoin.generator, simp, rule op_adjoin.scalar)
   show ?case
   proof (cases "T=x_op")
     case True
     show ?thesis by (rule bexI[of _ x_op]) (use x True xmember in \<open>simp_all only: True xmember x\<close>)
   next
     case False
     have Teq: "T=y_op" using alternatives False by blast
     show ?thesis by (rule bexI[of _ "y_op+op_scalar c"])
       (use y Teq ymember in \<open>simp_all only: Teq ymember y\<close>)
   qed
 next
   case (scalar z)
   have member: "op_scalar z\<in>op_adjoin {x_op,y_op}"
     by (rule op_adjoin.scalar)
   show ?case
     by (rule bexI[of _ "op_scalar z"])
       (simp_all only: horizontal_lift_scalar ramified_hom_scalar[OF H] member)
 next
   case (add T U)
   obtain R S where R: "R\<in>op_adjoin {x_op,y_op}" and S: "S\<in>op_adjoin {x_op,y_op}"
     and LR: "?L R=?C (?L T)" and LS: "?L S=?C (?L U)"
     using add.IH by blast
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra"
     using add.hyps unfolding weyl_algebra_def by blast+
   have RC: "R\<in>weyl_algebra" and SC: "S\<in>weyl_algebra"
     using R S unfolding weyl_algebra_def by blast+
   have member: "R+S\<in>op_adjoin {x_op,y_op}"
     by (rule op_adjoin.add[OF R S])
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
   have member: "R-S\<in>op_adjoin {x_op,y_op}"
     by (rule op_adjoin.diff[OF R S])
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
   have member: "op_comp R S\<in>op_adjoin {x_op,y_op}"
     by (rule op_adjoin.comp[OF R S])
   show ?case by (rule bexI[of _ "op_comp R S"])
     (simp_all only: polynomial_ramified_lift_comp[OF positive RC SC]
       polynomial_ramified_lift_comp[OF positive TC UC] LR LS
       ramified_hom_comp[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier] member)
 qed
qed

definition horizontal_polynomial_cut :: "complex \<Rightarrow> complex poly_operator \<Rightarrow> complex poly_operator" where
 "horizontal_polynomial_cut c P=(SOME R. R\<in>weyl_algebra \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"

lemma horizontal_polynomial_cut_spec:
 assumes P: "P\<in>weyl_algebra"
 shows "horizontal_polynomial_cut c P\<in>weyl_algebra \<and>
   polynomial_ramified_lift 1 (horizontal_polynomial_cut c P)=
     ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"
 unfolding horizontal_polynomial_cut_def
 by (rule someI_ex[where P="\<lambda>R. R\<in>weyl_algebra \<and> polynomial_ramified_lift 1 R=
   ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"])
   (use horizontal_cut_has_polynomial_preimage[where c=c, OF P] in blast)

lemma horizontal_polynomial_cut_carrier:
 "P\<in>weyl_algebra \<Longrightarrow> horizontal_polynomial_cut c P\<in>weyl_algebra"
 using horizontal_polynomial_cut_spec by blast

lemma horizontal_polynomial_cut_lift:
 "P\<in>weyl_algebra \<Longrightarrow> polynomial_ramified_lift 1 (horizontal_polynomial_cut c P)=
   ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"
 using horizontal_polynomial_cut_spec by blast

lemma horizontal_polynomial_cut_inverse:
 assumes P: "P\<in>weyl_algebra"
 shows "horizontal_polynomial_cut (-c) (horizontal_polynomial_cut c P)=P"
proof (rule polynomial_ramified_lift_injective[where l=1])
 show "0<(1::nat)" by simp
 show "horizontal_polynomial_cut (-c) (horizontal_polynomial_cut c P)\<in>weyl_algebra"
   by (intro horizontal_polynomial_cut_carrier P)
 show "P\<in>weyl_algebra" by (rule P)
 show "polynomial_ramified_lift 1 (horizontal_polynomial_cut (-c) (horizontal_polynomial_cut c P))=
   polynomial_ramified_lift 1 P"
   by (simp only: horizontal_polynomial_cut_lift[OF horizontal_polynomial_cut_carrier[OF P]]
     horizontal_polynomial_cut_lift[OF P]
     horizontal_cut_inverse_apply[OF polynomial_ramified_lift_carrier])
qed

lemma horizontal_polynomial_cut_scalar:
 "horizontal_polynomial_cut c (op_scalar z)=op_scalar z"
proof (rule polynomial_ramified_lift_injective[where l=1])
 show "0<(1::nat)" by simp
 show "horizontal_polynomial_cut c (op_scalar z)\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier) (simp add: weyl_algebra_def op_adjoin.scalar)
 show "op_scalar z\<in>(weyl_algebra::complex poly_operator set)"
   by (simp add: weyl_algebra_def op_adjoin.scalar)
 show "polynomial_ramified_lift 1 (horizontal_polynomial_cut c (op_scalar z))=
   polynomial_ramified_lift 1 (op_scalar z)"
 proof -
   have carrier: "op_scalar z\<in>(weyl_algebra::complex poly_operator set)"
     unfolding weyl_algebra_def by (rule op_adjoin.scalar)
   have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 0 c)"
     by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
   show ?thesis by (simp only: horizontal_polynomial_cut_lift[OF carrier] horizontal_lift_scalar ramified_hom_scalar[OF H])
 qed
qed

lemma horizontal_polynomial_cut_add:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "horizontal_polynomial_cut c (P+Q)=horizontal_polynomial_cut c P+horizontal_polynomial_cut c Q"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "horizontal_polynomial_cut c P\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF P])
 have EQ: "horizontal_polynomial_cut c Q\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF Q])
 have source: "P+Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "horizontal_polynomial_cut c P+horizontal_polynomial_cut c Q\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "horizontal_polynomial_cut c (P+Q)\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 0 c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (horizontal_polynomial_cut c (P+Q))=
   polynomial_ramified_lift 1 (horizontal_polynomial_cut c P+horizontal_polynomial_cut c Q)"
   by (simp only: horizontal_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_add[OF positive P Q]
     polynomial_ramified_lift_add[OF positive EP EQ]
     horizontal_polynomial_cut_lift[OF P] horizontal_polynomial_cut_lift[OF Q]
     ramified_hom_add[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma horizontal_polynomial_cut_diff:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "horizontal_polynomial_cut c (P-Q)=horizontal_polynomial_cut c P-horizontal_polynomial_cut c Q"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "horizontal_polynomial_cut c P\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF P])
 have EQ: "horizontal_polynomial_cut c Q\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF Q])
 have source: "P-Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "horizontal_polynomial_cut c P-horizontal_polynomial_cut c Q\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "horizontal_polynomial_cut c (P-Q)\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 0 c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (horizontal_polynomial_cut c (P-Q))=
   polynomial_ramified_lift 1 (horizontal_polynomial_cut c P-horizontal_polynomial_cut c Q)"
   by (simp only: horizontal_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_diff[OF positive P Q]
     polynomial_ramified_lift_diff[OF positive EP EQ]
     horizontal_polynomial_cut_lift[OF P] horizontal_polynomial_cut_lift[OF Q]
     ramified_hom_diff[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma horizontal_polynomial_cut_comp:
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 shows "horizontal_polynomial_cut c (op_comp P Q)=op_comp (horizontal_polynomial_cut c P) (horizontal_polynomial_cut c Q)"
proof -
 have positive: "0<(1::nat)" by simp
 have EP: "horizontal_polynomial_cut c P\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF P])
 have EQ: "horizontal_polynomial_cut c Q\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF Q])
 have source: "op_comp P Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast
 have target: "op_comp (horizontal_polynomial_cut c P) (horizontal_polynomial_cut c Q)\<in>weyl_algebra"
   using weyl_subalgebra EP EQ unfolding op_subalgebra_def by blast
 have Esource: "horizontal_polynomial_cut c (op_comp P Q)\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF source])
 have H: "ramified_alg_hom_on 1 (ramified_cut_aut 1 1 0 c)"
   by (simp add: ramified_cut_aut_def ramified_shear_hom_carrier)
 have equality: "polynomial_ramified_lift 1 (horizontal_polynomial_cut c (op_comp P Q))=
   polynomial_ramified_lift 1 (op_comp (horizontal_polynomial_cut c P) (horizontal_polynomial_cut c Q))"
   by (simp only: horizontal_polynomial_cut_lift[OF source]
     polynomial_ramified_lift_comp[OF positive P Q]
     polynomial_ramified_lift_comp[OF positive EP EQ]
     horizontal_polynomial_cut_lift[OF P] horizontal_polynomial_cut_lift[OF Q]
     ramified_hom_comp[OF H polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])
 show ?thesis by (rule polynomial_ramified_lift_injective[OF positive Esource target equality])
qed

lemma horizontal_polynomial_cut_id:
 "horizontal_polynomial_cut c id=id"
proof -
 have scalar: "(op_scalar 1::complex poly_operator)=id"
   by (rule ext) (simp add: op_scalar_def)
 show ?thesis using horizontal_polynomial_cut_scalar[of c 1] by (simp only: scalar)
qed

definition polynomial_alg_hom_on :: "(complex poly_operator \<Rightarrow> complex poly_operator) \<Rightarrow> bool" where
 "polynomial_alg_hom_on E \<longleftrightarrow>
 (\<forall>P\<in>weyl_algebra. E P\<in>weyl_algebra) \<and>
 (\<forall>c. E (op_scalar c)=op_scalar c) \<and>
 (\<forall>P\<in>weyl_algebra. \<forall>Q\<in>weyl_algebra.
   E(P+Q)=E P+E Q \<and> E(P-Q)=E P-E Q \<and>
   E(op_comp P Q)=op_comp(E P)(E Q))"

definition polynomial_alg_aut_on :: "(complex poly_operator \<Rightarrow> complex poly_operator) \<Rightarrow>
 (complex poly_operator \<Rightarrow> complex poly_operator) \<Rightarrow> bool" where
 "polynomial_alg_aut_on E H \<longleftrightarrow> polynomial_alg_hom_on E \<and>
 polynomial_alg_hom_on H \<and> (\<forall>P\<in>weyl_algebra. H(E P)=P \<and> E(H P)=P)"

lemma horizontal_polynomial_cut_hom:
 "polynomial_alg_hom_on (horizontal_polynomial_cut c)"
 by (auto simp only: polynomial_alg_hom_on_def intro: horizontal_polynomial_cut_carrier
   horizontal_polynomial_cut_scalar horizontal_polynomial_cut_add
   horizontal_polynomial_cut_diff horizontal_polynomial_cut_comp)

lemma horizontal_cut_has_polynomial_automorphism:
 "\<exists>E H. polynomial_alg_aut_on E H \<and> (\<forall>P\<in>weyl_algebra.
   polynomial_ramified_lift 1 (E P)=
     ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
proof -
 have aut: "polynomial_alg_aut_on (horizontal_polynomial_cut c) (horizontal_polynomial_cut (-c))"
   unfolding polynomial_alg_aut_on_def
   using horizontal_polynomial_cut_hom[of c] horizontal_polynomial_cut_hom[of "-c"]
     horizontal_polynomial_cut_inverse[where c=c] horizontal_polynomial_cut_inverse[where c="-c"]
   by auto
 show ?thesis by (intro exI[of _ "horizontal_polynomial_cut c"]
     exI[of _ "horizontal_polynomial_cut (-c)"])
   (use aut horizontal_polynomial_cut_lift in blast)
qed

lemma horizontal_polynomial_cut_adjoin_image:
 assumes generators: "G\<subseteq>(weyl_algebra::complex poly_operator set)"
 and member: "T\<in>op_adjoin G"
 shows "horizontal_polynomial_cut c T\<in>op_adjoin (horizontal_polynomial_cut c ` G)"
proof -
 from member have "T\<in>weyl_algebra \<and>
   horizontal_polynomial_cut c T\<in>op_adjoin (horizontal_polynomial_cut c ` G)"
 proof (induction rule: op_adjoin.induct)
   case (generator T)
   then show ?case using generators by (auto intro: op_adjoin.generator)
 next
   case (scalar z)
   then show ?case by (simp add: horizontal_polynomial_cut_scalar weyl_algebra_def op_adjoin.scalar)
 next
   case (add T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra" using add.IH by blast+
   have target: "T+U\<in>weyl_algebra" using TC UC weyl_subalgebra unfolding op_subalgebra_def by blast
   have image: "horizontal_polynomial_cut c (T+U)\<in>op_adjoin(horizontal_polynomial_cut c ` G)"
     by (simp only: horizontal_polynomial_cut_add[OF TC UC])
       (rule op_adjoin.add; use add.IH in blast)
   show ?case using target image by blast
 next
   case (diff T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra" using diff.IH by blast+
   have target: "T-U\<in>weyl_algebra" using TC UC weyl_subalgebra unfolding op_subalgebra_def by blast
   have image: "horizontal_polynomial_cut c (T-U)\<in>op_adjoin(horizontal_polynomial_cut c ` G)"
     by (simp only: horizontal_polynomial_cut_diff[OF TC UC])
       (rule op_adjoin.diff; use diff.IH in blast)
   show ?case using target image by blast
 next
   case (comp T U)
   have TC: "T\<in>weyl_algebra" and UC: "U\<in>weyl_algebra" using comp.IH by blast+
   have target: "op_comp T U\<in>weyl_algebra" using TC UC weyl_subalgebra unfolding op_subalgebra_def by blast
   have image: "horizontal_polynomial_cut c (op_comp T U)\<in>op_adjoin(horizontal_polynomial_cut c ` G)"
     by (simp only: horizontal_polynomial_cut_comp[OF TC UC])
       (rule op_adjoin.comp; use comp.IH in blast)
   show ?case using target image by blast
 qed
 then show ?thesis by blast
qed

lemma horizontal_cut_recovers_polynomial_counterexample:
 assumes pair: "is_counterexample_pair P Q"
 shows "\<exists>R S. is_counterexample_pair R S \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P) \<and>
   polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q)"
proof -
 let ?R="horizontal_polynomial_cut c P"
 let ?S="horizontal_polynomial_cut c Q"
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   using pair unfolding is_counterexample_pair_def by blast+
 have R: "?R\<in>weyl_algebra" and S: "?S\<in>weyl_algebra"
   by (rule horizontal_polynomial_cut_carrier[OF P], rule horizontal_polynomial_cut_carrier[OF Q])
 have exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast
 have QP: "op_comp Q P\<in>weyl_algebra" and PQ: "op_comp P Q\<in>weyl_algebra"
   using weyl_subalgebra P Q unfolding op_subalgebra_def by blast+
 have image_exact: "op_comp ?S ?R-op_comp ?R ?S=id"
   using arg_cong[OF exact, of "horizontal_polynomial_cut c"]
   by (simp only: horizontal_polynomial_cut_diff[OF QP PQ]
      horizontal_polynomial_cut_comp[OF Q P] horizontal_polynomial_cut_comp[OF P Q]
      horizontal_polynomial_cut_id)
 have nongeneration: "op_adjoin {?R,?S}\<noteq>weyl_algebra"
 proof
   assume generation: "op_adjoin {?R,?S}=weyl_algebra"
   have reverse: "weyl_algebra\<subseteq>op_adjoin {P,Q}"
   proof
     fix T::"complex poly_operator" assume T: "T\<in>weyl_algebra"
     have ET: "horizontal_polynomial_cut c T\<in>op_adjoin {?R,?S}"
       using horizontal_polynomial_cut_carrier[OF T] generation by simp
     have generators: "{?R,?S}\<subseteq>weyl_algebra" using R S by auto
     have recovered: "horizontal_polynomial_cut (-c) (horizontal_polynomial_cut c T)
       \<in>op_adjoin (horizontal_polynomial_cut (-c) ` {?R,?S})"
       by (rule horizontal_polynomial_cut_adjoin_image[OF generators ET])
     show "T\<in>op_adjoin {P,Q}" using recovered
       by (simp only: horizontal_polynomial_cut_inverse[OF T]
         image_insert image_empty horizontal_polynomial_cut_inverse[OF P]
         horizontal_polynomial_cut_inverse[OF Q])
   qed
   have forward: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
     by (rule pair_generated_inside_weyl[OF P Q])
   have "op_adjoin {P,Q}=weyl_algebra" using forward reverse by blast
   then show False using pair unfolding is_counterexample_pair_def by blast
 qed
 have actual_pair: "is_counterexample_pair ?R ?S"
   using R S image_exact nongeneration unfolding is_counterexample_pair_def by blast
 show ?thesis by (intro exI[of _ ?R] exI[of _ ?S])
   (use actual_pair horizontal_polynomial_cut_lift[OF P]
      horizontal_polynomial_cut_lift[OF Q] in blast)
qed

end
