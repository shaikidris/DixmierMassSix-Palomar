theory Diagonal_Cut_Factorization
 imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

text \<open>Exact independent scalar producer from GGVDiagonalCutFactorization.lean
at 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

lemma complex_polynomial_two_root_factorization:
 fixes p::"complex poly"
 assumes nonzero: "p\<noteq>0" and root_bound: "card(set_mset(proots p))\<le>2"
 shows "(\<exists>lam::complex. lam\<noteq>0 \<and> p=[:lam:]) \<or>
 (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and>
 p=[:lam:]*[:-alpha,1:]^k) \<or>
 (\<exists>lam alpha beta::complex. \<exists>u v::nat.
 lam\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>u \<and> 1\<le>v \<and>
 p=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v)"
proof -
 let ?S="set_mset(proots p)"
 have finite_roots: "finite ?S" by simp
 have roots_eq: "?S={z. poly p z=0}" using nonzero by auto
 have leading: "lead_coeff p\<noteq>0" using nonzero by simp
 have decomposition: "p=[:lead_coeff p:]*(\<Prod>z\<in>?S. [:-z,1:]^order z p)"
   using complex_poly_decompose[of p] by (simp add: roots_eq)
 have multiplicity: "1\<le>order z p" if "z\<in>?S" for z
   using that nonzero by (auto simp: roots_eq order_root)
 show ?thesis
 proof (cases "?S={}")
   case True
   have shape: "p=[:lead_coeff p:]" using decomposition by (simp only: True prod.empty mult_1_right)
   show ?thesis using leading shape by blast
 next
   case False
   have card_positive: "0<card ?S"
     by (rule iffD2[OF card_gt_0_iff]) (rule conjI[OF False finite_roots])
   show ?thesis
   proof (cases "card ?S=1")
     case True
     obtain alpha where shape_set: "?S={alpha}" using True by (auto simp: card_Suc_eq)
     have alpha: "alpha\<in>?S" using shape_set by simp
     have shape: "p=[:lead_coeff p:]*[:-alpha,1:]^order alpha p"
       using decomposition by (simp add: shape_set prod.insert prod.empty)
     show ?thesis using leading multiplicity[OF alpha] shape by blast
   next
     case False
     have card_two: "card ?S=Suc(Suc 0)" using root_bound card_positive False by arith
     obtain alpha T where alpha: "alpha\<notin>T" and set_shape: "?S=insert alpha T"
       and card_T: "card T=Suc 0"
       using card_eq_SucD[OF card_two] by blast
     obtain beta where T_shape: "T={beta}" using card_T by (auto simp: card_Suc_eq)
     have different: "alpha\<noteq>beta" using alpha T_shape by simp
     have alpha_member: "alpha\<in>?S" and beta_member: "beta\<in>?S"
       using set_shape T_shape by simp_all
     have shape: "p=[:lead_coeff p:]*[:-alpha,1:]^order alpha p*[:-beta,1:]^order beta p"
       using decomposition by (simp add: set_shape T_shape different mult.assoc)
     show ?thesis using leading different multiplicity[OF alpha_member]
       multiplicity[OF beta_member] shape by blast
   qed
 qed
qed

end
