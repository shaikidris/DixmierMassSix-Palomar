theory Ramified_Joseph_Two_Bracket
  imports "Ramified_Commutator_Top_Face"
    "Polynomial_Finite_Cut_Dimension_Witness"
begin

lemma ramifiedJosephChain_carrier:
  assumes P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
  shows "ramifiedJosephChain P R n\<in>ramified_operator_algebra l"
proof (induction n)
  case 0 show ?case by (simp only: ramifiedJosephChain.simps; rule R)
next
  case (Suc n)
  have carrier: "laurent_comp P (ramifiedJosephChain P R n)-laurent_comp (ramifiedJosephChain P R n) P\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_diff[OF ramified_algebra_comp[OF P Suc.IH] ramified_algebra_comp[OF Suc.IH P]])
  show ?case by (simp only: ramifiedJosephChain.simps; rule carrier)
qed

definition RamifiedJosephTwoBracketAt where
  "RamifiedJosephTwoBracketAt l rho sigma P R n \<longleftrightarrow>
    ramified_face_centralization l rho sigma P (ramifiedJosephChain P R n)\<noteq>0 \<and>
    ramifiedJosephChain P R (Suc n)\<noteq>0 \<and>
    ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R (Suc n))=
      -ramified_face_centralization l rho sigma P (ramifiedJosephChain P R n) \<and>
    ramified_weight_deg l rho sigma (ramifiedJosephChain P R (Suc n))=
      ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma (ramifiedJosephChain P R n)-int l*(rho+sigma) \<and>
    ramified_face_centralization l rho sigma P (ramifiedJosephChain P R (Suc n))=0"

lemma ramified_two_bracket_of_terminating_chain:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and first: "ramified_face_centralization l rho sigma P R\<noteq>0"
    and terminal: "\<exists>n. ramifiedJosephChain P R n=0"
  shows "\<exists>n. RamifiedJosephTwoBracketAt l rho sigma P R n"
proof -
  let ?B = "\<lambda>n. ramified_face_centralization l rho sigma P (ramifiedJosephChain P R n)"
  obtain terminal_n where killed: "ramifiedJosephChain P R terminal_n=0" using terminal by blast
  have zero: "?B terminal_n=0" by (simp only: killed ramified_face_centralization_zero_right[OF l])
  have exists: "\<exists>n. ?B n=0" by (rule exI[of _ terminal_n]) (rule zero)
  let ?N = "LEAST n. ?B n=0"
  have N: "?B ?N=0" by (rule LeastI_ex[OF exists])
  have Npos: "0<?N" using N first by (cases ?N) auto
  have prev: "?B (?N-1)\<noteq>0"
  proof
    assume zero: "?B (?N-1)=0"
    have "?N\<le>?N-1" by (rule Least_le[where P="\<lambda>n. ?B n=0" and k="?N-1"]) (rule zero)
    then show False using Npos by arith
  qed
  let ?T = "ramifiedJosephChain P R (?N-1)"
  have T: "?T\<in>ramified_operator_algebra l" by (rule ramifiedJosephChain_carrier[OF P R])
  have Tnz: "?T\<noteq>0"
  proof
    assume zeroT: "?T=0"
    have zeroB: "?B (?N-1)=0"
      by (subst zeroT; rule ramified_face_centralization_zero_right[OF l])
    show False using prev zeroB by contradiction
  qed
  have bracket: "ramified_face_bracket l rho sigma P ?T\<noteq>0"
    by (simp only: ramified_face_bracket_eq_neg_centralization) (use prev in simp)
  have successor: "ramifiedJosephChain P R ?N=laurent_comp P ?T-laurent_comp ?T P"
  proof -
    have index: "?N=Suc(?N-1)" using Npos by arith
    show ?thesis by (subst (1) index) (rule ramifiedJosephChain.simps)
  qed
  have face: "ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R ?N)=-?B (?N-1)"
    by (simp only: successor ramified_noncentralizing_commutator_top_face[OF l rho positive P T Pnz Tnz bracket]
      ramified_face_bracket_eq_neg_centralization)
  have degree: "ramified_weight_deg l rho sigma (ramifiedJosephChain P R ?N)=
    ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma ?T-int l*(rho+sigma)"
    by (simp only: successor ramified_noncentralizing_commutator_weight[OF l rho positive P T Pnz Tnz bracket])
  have nextnz: "ramifiedJosephChain P R ?N\<noteq>0"
  proof
    assume killed: "ramifiedJosephChain P R ?N=0"
    have "?B (?N-1)=0" using face by (simp only: killed ramified_top_face_polynomial_zero[OF l]) simp
    then show False using prev by contradiction
  qed
  have index: "Suc(?N-1)=?N" using Npos by arith
  show ?thesis by (intro exI[of _ "?N-1"])
    (simp only: RamifiedJosephTwoBracketAt_def index; intro conjI prev nextnz face degree N)
qed

lemma finite_cut_generated_two_bracket_exists:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and history: "admissible_ramified_history l cuts"
    and rho: "0<rho" and positive: "0<rho+sigma"
    and Unz: "finite_cut_image l cuts P\<noteq>0"
    and degree: "ramified_weight_deg l rho sigma (finite_cut_image l cuts P)\<noteq>0"
  shows "\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    (\<exists>n. RamifiedJosephTwoBracketAt l rho sigma (finite_cut_image l cuts P) (finite_cut_image l cuts R) n)"
proof -
  obtain R where R: "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}"
    "ramified_face_centralization l rho sigma (finite_cut_image l cuts P) (finite_cut_image l cuts R)\<noteq>0"
    using finite_cut_generated_noncentralizing_face_exists[OF l P Q exact history rho finite_cut_image_carrier[OF l] Unz degree] by blast
  have terminal: "\<exists>n. ramifiedJosephChain (finite_cut_image l cuts P) (finite_cut_image l cuts R) n=0"
    by (rule ramified_generated_chain_terminates_of_finite_cut_map[OF l P Q exact R(2)])
  have witness: "\<exists>n. RamifiedJosephTwoBracketAt l rho sigma (finite_cut_image l cuts P) (finite_cut_image l cuts R) n"
    by (rule ramified_two_bracket_of_terminating_chain[OF l rho positive finite_cut_image_carrier[OF l]
      finite_cut_image_carrier[OF l] Unz R(3) terminal])
  show ?thesis by (intro exI[of _ R] conjI R(1,2) witness)
qed

end
