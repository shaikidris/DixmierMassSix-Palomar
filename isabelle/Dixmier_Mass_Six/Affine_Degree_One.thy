theory Affine_Degree_One
 imports Affine_Pair_Generation
   "One_Sided_Generator_Extraction"
begin

lemma pbwCoeff_eq_zero_of_totalDeg_one:
 fixes T :: "complex poly_operator"
 assumes carrier: "T\<in>weyl_algebra" and degree: "total_degree T=1"
   and high: "2\<le>i+j"
 shows "pbw_coeff T i j=0"
proof (rule ccontr)
 assume nonzero: "pbw_coeff T i j\<noteq>0"
 have member: "(i,j)\<in>biv_support (pbw_symbol T)"
   using nonzero by (simp add: biv_support_def weyl_symbol_coeff[OF carrier])
 have image_member: "(\<lambda>u. fst u+snd u) (i,j)\<in>
   (\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol T)" by (rule imageI[OF member])
 have index_member: "i+j\<in>insert 0 ((\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol T))"
   using image_member by simp
 have bound: "i+j\<le>total_degree T"
   unfolding total_degree_def by (rule Max_ge) (simp, rule index_member)
 show False using bound high degree by arith
qed

lemma affine_native_in_weyl:
 "op_scalar c+(\<lambda>p. smult a (x_op p))+(\<lambda>p. smult b (y_op p))
   \<in>(weyl_algebra::complex poly_operator set)"
 unfolding weyl_algebra_def
 by (intro op_adjoin.add op_adjoin.scalar op_adjoin_smult)
    (auto intro: op_adjoin.generator)

lemma affine_native_coeff:
 "pbw_coeff (op_scalar c+(\<lambda>p. smult a (x_op p))+(\<lambda>p. smult b (y_op p))) i j =
   (if i=0\<and>j=0 then c else 0)+(if i=1\<and>j=0 then a else 0)+(if i=0\<and>j=1 then b else 0)"
 for a b c :: complex
proof -
 have x: "(x_op::complex poly_operator)=normal_monomial 1 0"
   by (rule ext) (simp add: normal_monomial_apply x_op_def)
 have y: "(y_op::complex poly_operator)=normal_monomial 0 1"
   by (rule ext) (simp add: normal_monomial_apply y_op_def)
 have scalar: "op_scalar c=(\<lambda>p. smult c (normal_monomial 0 0 p))"
   by (simp add: op_scalar_def)
 show ?thesis
   by (simp only: pbw_coeff_add x y scalar pbw_coeff_smult pbw_coeff_normal_monomial;
       simp)
qed

lemma affine_reconstruction_of_totalDeg_one:
 fixes T :: "complex poly_operator"
 assumes carrier: "T\<in>weyl_algebra" and degree: "total_degree T=1"
 shows "T= op_scalar (pbw_coeff T 0 0)+
   (\<lambda>p. smult (pbw_coeff T 1 0) (x_op p))+
   (\<lambda>p. smult (pbw_coeff T 0 1) (y_op p))"
proof (rule weyl_pbw_injective[OF carrier affine_native_in_weyl])
 fix i j
 show "pbw_coeff T i j = pbw_coeff
   (op_scalar (pbw_coeff T 0 0)+(\<lambda>p. smult (pbw_coeff T 1 0) (x_op p))+
   (\<lambda>p. smult (pbw_coeff T 0 1) (y_op p))) i j"
 proof (cases "i+j\<le>1")
   case True
   have cases: "(i=0\<and>j=0)\<or>(i=1\<and>j=0)\<or>(i=0\<and>j=1)" using True by arith
   then show ?thesis by (elim disjE) (simp_all add: affine_native_coeff)
 next
   case False
   have high: "2\<le>i+j" using False by arith
   have zero: "pbw_coeff T i j=0"
     by (rule pbwCoeff_eq_zero_of_totalDeg_one[OF carrier degree high])
   show ?thesis using high by (simp only: affine_native_coeff zero; auto)
 qed
qed

lemma leadingForm_linear_coeff_of_vDeg_one:
 fixes T :: "complex poly_operator"
 assumes carrier: "T\<in>weyl_algebra" and degree: "v_degree 1 1 T=1"
   and index: "i+j=1"
 shows "biv_coeff (leading_form 1 1 T) i j=pbw_coeff T i j"
proof -
 have cast_index: "int(i+j)=1" using arg_cong[OF index, of int] by simp
 have weight: "pair_weight 1 1 (i,j)=1"
   using cast_index by (simp add: pair_weight_def)
 show ?thesis by (simp only: leading_form_def weighted_component_coeff degree weight
   if_True weyl_symbol_coeff[OF carrier]; simp)
qed

lemma affine_determinant_one_of_diagonal_bracket_one:
 fixes P Q :: "complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and P_degree: "v_degree 1 1 P=1" and Q_degree: "v_degree 1 1 Q=1"
   and bracket: "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)=1"
 shows "pbw_coeff Q 0 1*pbw_coeff P 1 0-pbw_coeff Q 1 0*pbw_coeff P 0 1=1"
proof -
 have constant_coefficient: "biv_coeff (biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)) 0 0=1"
   using bracket by (simp add: biv_coeff_def)
 have Px: "biv_coeff (leading_form 1 1 P) 1 0=pbw_coeff P 1 0"
   by (rule leadingForm_linear_coeff_of_vDeg_one[OF P P_degree]) simp
 have Py: "biv_coeff (leading_form 1 1 P) 0 1=pbw_coeff P 0 1"
   by (rule leadingForm_linear_coeff_of_vDeg_one[OF P P_degree]) simp
 have Qx: "biv_coeff (leading_form 1 1 Q) 1 0=pbw_coeff Q 1 0"
   by (rule leadingForm_linear_coeff_of_vDeg_one[OF Q Q_degree]) simp
 have Qy: "biv_coeff (leading_form 1 1 Q) 0 1=pbw_coeff Q 0 1"
   by (rule leadingForm_linear_coeff_of_vDeg_one[OF Q Q_degree]) simp
 show ?thesis using constant_coefficient
   by (simp only: poisson_coeff_zero Px Py Qx Qy)
qed

end
