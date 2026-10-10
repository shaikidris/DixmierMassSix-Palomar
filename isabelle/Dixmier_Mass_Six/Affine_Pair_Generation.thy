theory Affine_Pair_Generation
 imports "GGV_Grade_Normalization"
begin

text \<open>Exact unit-determinant generation architecture from
AffineExactPair.lean, source 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.
The source subtype carrier is explicit in the native representation.\<close>

lemma affine_pair_generates_of_unit_determinant:
 fixes P Q :: "complex poly_operator" and a b c d e f :: complex
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and P_form: "P= op_scalar c+(\<lambda>p. smult a (x_op p))+(\<lambda>p. smult b (y_op p))"
   and Q_form: "Q= op_scalar f+(\<lambda>p. smult d (x_op p))+(\<lambda>p. smult e (y_op p))"
   and determinant: "e*a-d*b=1"
 shows "op_adjoin {P,Q}=weyl_algebra"
proof -
 let ?S = "op_adjoin {P,Q}"
 have P_mem: "P\<in>?S" and Q_mem: "Q\<in>?S"
   by (auto intro: op_adjoin.generator)
 have x_expression: "x_op=(\<lambda>p. smult e (P p))-(\<lambda>p. smult b (Q p))-op_scalar (e*c-b*f)"
 proof (rule ext)
   fix p
   have expand: "smult e (P p)-smult b (Q p)-smult (e*c-b*f) p =
     smult (e*a-d*b) (x_op p)"
     by (simp add: P_form Q_form op_scalar_def smult_add_right smult_diff_right
       smult_smult smult_diff_left smult_add_left algebra_simps)
   show "x_op p=((\<lambda>p. smult e (P p))-(\<lambda>p. smult b (Q p))-op_scalar (e*c-b*f)) p"
     using expand by (simp add: op_scalar_def determinant)
 qed
 have y_expression: "y_op=(\<lambda>p. smult a (Q p))-(\<lambda>p. smult d (P p))-op_scalar (a*f-d*c)"
 proof (rule ext)
   fix p
   have expand: "smult a (Q p)-smult d (P p)-smult (a*f-d*c) p =
     smult (e*a-d*b) (y_op p)"
     by (simp add: P_form Q_form op_scalar_def smult_add_right smult_diff_right
       smult_smult smult_diff_left smult_add_left algebra_simps)
   show "y_op p=((\<lambda>p. smult a (Q p))-(\<lambda>p. smult d (P p))-op_scalar (a*f-d*c)) p"
     using expand by (simp add: op_scalar_def determinant)
 qed
 have x_mem: "x_op\<in>?S"
   using op_adjoin.diff[OF op_adjoin.diff[OF op_adjoin_smult[OF P_mem, of e]
      op_adjoin_smult[OF Q_mem, of b]] op_adjoin.scalar[of "e*c-b*f" "{P,Q}"]]
   by (simp only: x_expression)
 have y_mem: "y_op\<in>?S"
   using op_adjoin.diff[OF op_adjoin.diff[OF op_adjoin_smult[OF Q_mem, of a]
      op_adjoin_smult[OF P_mem, of d]] op_adjoin.scalar[of "a*f-d*c" "{P,Q}"]]
   by (simp only: y_expression)
 have inside: "?S\<subseteq>weyl_algebra"
   by (rule weyl_nested_adjoin) (use P Q in auto)
 have closed: "op_subalgebra ?S"
   by (rule op_adjoin_subalgebra) (use P Q in \<open>auto intro: weyl_linear\<close>)
 show ?thesis by (rule adjoin_eq_top_of_xy_mem[OF inside closed x_mem y_mem])
qed

end
