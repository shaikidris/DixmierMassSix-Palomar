theory Polynomial_Cut_Translation
 imports "Polynomial_Monomial_Shear_Recovery"
   "Polynomial_Companion_Cut_Grade"
begin

lemma native_pcompose_power:
 "pcompose (p^k) q=(pcompose p q)^k"
 for p q::"complex poly"
 by (induction k) (simp_all add: pcompose_1 pcompose_mult)

lemma polynomial_monomial_cut_weight_and_translate:
 fixes P R::"complex poly_operator" and sigma::nat and c::complex
 assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra" and Pnz: "P\<noteq>0"
 and positive: "0<v_degree 1 (int sigma) P" and Rpositive: "0<v_degree 1 (int sigma) R"
 and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P)"
 shows "v_degree 1 (int sigma) R=v_degree 1 (int sigma) P \<and>
   cut_poly 1 (int sigma) R=pcompose (cut_poly 1 (int sigma) P) [:c,1:]"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have sum: "0<(1::int)+int sigma" by simp
 have zero_carrier: "(0::complex poly_operator)\<in>weyl_algebra" by (simp add: weyl_algebra_def)
 have lift_nz: "polynomial_ramified_lift 1 P\<noteq>0"
   using polynomial_ramified_lift_injective[OF one P zero_carrier] Pnz by auto
 have weight: "ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 P)=v_degree 1 (int sigma) P"
   by (simp only: polynomial_ramified_lift_weight_degree[OF one P]; simp)
 have shear: "ramified_weight_deg 1 1 (int sigma) (ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P))=v_degree 1 (int sigma) P \<and>
   ramified_top_face_polynomial 1 1 (int sigma) (ramified_cut_aut 1 1 (int sigma) c (polynomial_ramified_lift 1 P))=
   pcompose (ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 P)) [:c,1:]"
 proof -
   have scaled_weight: "ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 P)=1*v_degree 1 (int sigma) P"
     by (simp only: weight mult_1_left)
   note translated = ramified_cut_aut_top_face_eq_translate_of_weight[
     where l=1 and T="polynomial_ramified_lift 1 P" and rho=1 and sigma="int sigma"
       and c=c and r="v_degree 1 (int sigma) P",
     OF one polynomial_ramified_lift_carrier rho divides sum lift_nz scaled_weight]
   show ?thesis using translated by (simp only: mult_1_left)
 qed
 show ?thesis using shear
   by (simp only: recover[symmetric] polynomial_ramified_lift_weight_degree[OF one R]
     polynomial_ramified_lift_top_face[OF one R rho divides]
     polynomial_ramified_lift_top_face[OF one P rho divides]; simp)
qed

lemma polynomial_monomial_cut_removes_root:
 fixes P Q::"complex poly_operator" and sigma k::nat and lam alpha::complex
 assumes pair: "is_counterexample_pair P Q"
 and cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
 shows "\<exists>R S::complex poly_operator. is_counterexample_pair R S \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P) \<and>
   v_degree 1 (int sigma) R=v_degree 1 (int sigma) P \<and>
   cut_poly 1 (int sigma) R=[:lam:]*[:0,1:]^k"
proof -
 obtain R S where RS: "is_counterexample_pair R S"
 and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P)"
   using polynomial_monomial_cut_recovers_polynomial_counterexample[where sigma=sigma and c=alpha, OF pair] by blast
 have P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   using pair RS by (simp_all add: is_counterexample_pair_def)
 have direction: "is_direction 1 (int sigma)" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 (int sigma) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Rpositive: "0<v_degree 1 (int sigma) R" by (rule counterexample_vDeg_pos_all_directions[OF RS direction])
 have Pnz: "P\<noteq>0" using positive by auto
 have translate: "v_degree 1 (int sigma) R=v_degree 1 (int sigma) P \<and>
   cut_poly 1 (int sigma) R=pcompose (cut_poly 1 (int sigma) P) [:alpha,1:]"
   by (rule polynomial_monomial_cut_weight_and_translate[OF P R Pnz positive Rpositive recover])
 have affine: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have newcut: "cut_poly 1 (int sigma) R=[:lam:]*[:0,1:]^k"
   using conjunct2[OF translate]
   by (simp add: cut pcompose_smult native_pcompose_power affine)
 show ?thesis by (intro exI[of _ R] exI[of _ S]) (use RS recover translate newcut in blast)
qed

end
