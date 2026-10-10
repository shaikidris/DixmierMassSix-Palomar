theory Positive_One_Root_Factorization
 imports "Diagonal_Cut_Factorization"
begin

lemma complex_polynomial_one_root_factorization:
 fixes p::"complex poly"
 assumes nonzero: "p\<noteq>0" and root_bound: "card(set_mset(proots p))\<le>1"
 shows "(\<exists>lam::complex. lam\<noteq>0 \<and> p=[:lam:]) \<or>
   (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and> p=[:lam:]*[:-alpha,1:]^k)"
proof -
 let ?S="set_mset(proots p)"
 have roots: "?S={z. poly p z=0}" using nonzero by auto
 have leading: "lead_coeff p\<noteq>0" using nonzero by simp
 have decomposition: "p=[:lead_coeff p:]*(\<Prod>z\<in>?S. [:-z,1:]^order z p)"
   using complex_poly_decompose[of p] by (simp add: roots)
 show ?thesis
 proof (cases "?S={}")
   case True
   have shape: "p=[:lead_coeff p:]" using decomposition by (simp only: True prod.empty mult_1_right)
   show ?thesis using leading shape by blast
 next
   case False
   have finiteS: "finite ?S" by simp
   have card_positive: "0<card ?S"
     by (rule iffD2[OF card_gt_0_iff conjI[OF False finiteS]])
   have cardinal: "card ?S=1" using root_bound card_positive by arith
   obtain alpha where singleton: "?S={alpha}" using cardinal by (auto simp: card_Suc_eq)
   have alpha: "poly p alpha=0" using singleton roots by blast
   have positive: "1\<le>order alpha p" using nonzero alpha by (simp add: order_root)
   have shape: "p=[:lead_coeff p:]*[:-alpha,1:]^order alpha p"
     using decomposition by (simp only: singleton prod.insert finite.emptyI empty_iff not_False_eq_True prod.empty mult_1_right)
   show ?thesis using leading positive shape by blast
 qed
qed

end
