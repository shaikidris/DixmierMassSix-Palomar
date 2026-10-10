theory Derivative_Bracket_Roots
 imports Diagonal_Lowest_Order
begin

lemma derivative_bracket_root_containment:
 fixes f g::"complex poly" and A B::complex
 assumes g: "g\<noteq>0" and B: "B\<noteq>0"
 and equation: "[:A:]*(pderiv f*g)-[:B:]*(f*pderiv g)=g"
 and root: "poly g z=0"
 shows "poly f z=0"
proof -
 have positive: "0<Polynomial.order z g" using order_gt_0_iff[OF g] root by simp
 obtain k where order: "Polynomial.order z g=Suc k"
   using positive by (cases "Polynomial.order z g") auto
 obtain u where shape: "g=[:-z,1:]^Suc k*u" and not_divides: "\<not>[:-z,1:] dvd u"
   using order_decomp[OF g, of z] unfolding order by blast
 have u: "poly u z\<noteq>0" using not_divides by (simp add: poly_eq_0_iff_dvd)
 let ?X="[:-z,1:]::complex poly"
 have derivative_X: "pderiv ?X=1" by (simp add: pderiv_pCons)
 have scalar: "smult c p=[:c:]*p" for c::complex and p::"complex poly" by simp
 have derivative: "pderiv g=?X^k*([:of_nat(Suc k):]*u+?X*pderiv u)"
   proof -
   have "pderiv g=pderiv(?X^Suc k*u)" by (rule arg_cong[OF shape])
   also have "...=?X^k*([:of_nat(Suc k):]*u+?X*pderiv u)"
   proof -
     have dpower: "pderiv(?X^Suc k)=[:of_nat(Suc k):]*?X^k"
       by (simp only: pderiv_power_Suc derivative_X scalar mult_1_right)
     show ?thesis by (simp only: pderiv_mult dpower; simp only: power_Suc; algebra)
   qed
   finally show ?thesis .
 qed
 have factor: "?X^k*([:A:]*(pderiv f*(?X*u))-
   [:B:]*(f*([:of_nat(Suc k):]*u+?X*pderiv u)))=?X^k*(?X*u)"
 proof -
   have left: "?X^k*([:A:]*(pderiv f*(?X*u))-
     [:B:]*(f*([:of_nat(Suc k):]*u+?X*pderiv u)))=
     [:A:]*(pderiv f*g)-[:B:]*(f*pderiv g)"
     by (subst derivative; subst shape; simp only: power_Suc; algebra)
   have right: "?X^k*(?X*u)=g" by (subst shape; simp only: power_Suc; algebra)
   show ?thesis by (simp only: left right equation)
 qed
 have nonzero: "?X^k\<noteq>0" by simp
 have reduced: "[:A:]*(pderiv f*(?X*u))-
   [:B:]*(f*([:of_nat(Suc k):]*u+?X*pderiv u))=?X*u"
   by (rule iffD1[OF mult_left_cancel[OF nonzero] factor])
 have at_root: "B*poly f z*of_nat(Suc k)*poly u z=0"
   using arg_cong[where f="\<lambda>p. poly p z", OF reduced]
   by (simp add: mult.assoc)
 have knz: "(of_nat(Suc k)::complex)\<noteq>0" by (simp only: of_nat_eq_0_iff Suc_not_Zero not_False_eq_True)
 have factors: "B=0 \<or> poly f z=0 \<or> (of_nat(Suc k)::complex)=0 \<or> poly u z=0"
   using at_root by (simp only: mult_eq_0_iff; blast)
 show ?thesis using factors B u knz by blast
qed

lemma derivative_bracket_root_count:
 fixes f g::"complex poly" and A B::complex
 assumes g: "g\<noteq>0" and B: "B\<noteq>0"
 and equation: "[:A:]*(pderiv f*g)-[:B:]*(f*pderiv g)=g"
 shows "card {z. poly g z=0}\<le>degree f"
proof -
 have f: "f\<noteq>0" using equation g by auto
 have subset: "{z. poly g z=0}\<subseteq>{z. poly f z=0}"
   using derivative_bracket_root_containment[OF g B equation] by blast
 have "card {z. poly g z=0}\<le>card {z. poly f z=0}"
   by (rule card_mono[OF poly_roots_finite[OF f] subset])
 also have "...\<le>degree f" by (rule card_poly_roots_bound[OF f])
 finally show ?thesis .
qed

lemma derivative_bracket_top_degree_balance:
 fixes f g::"complex poly" and A B::complex
 assumes gdegree: "0<degree g" and fdegree: "2\<le>degree f"
 and equation: "[:A:]*(pderiv f*g)-[:B:]*(f*pderiv g)=g"
 shows "A*of_nat(degree f)=B*of_nat(degree g)"
proof -
 let ?L="degree f" let ?e="degree g"
 let ?j="(?L-1)+?e"
 have f: "f\<noteq>0" using fdegree by auto
 have g: "g\<noteq>0" using gdegree by auto
 have topf: "coeff f ?L\<noteq>0" using f by simp
 have topg: "coeff g ?e\<noteq>0" using g by simp
 have indices: "?L+(?e-1)=?j" using fdegree gdegree by arith
 have findex: "Suc(?L-1)=?L" using fdegree by arith
 have gindex: "Suc(?e-1)=?e" using gdegree by arith
 have derivative_f: "coeff(pderiv f)(?L-1)=of_nat ?L*coeff f ?L"
   by (simp only: coeff_pderiv findex)
 have derivative_g: "coeff(pderiv g)(?e-1)=of_nat ?e*coeff g ?e"
   by (simp only: coeff_pderiv gindex)
 have first_product: "coeff(pderiv f*g) ?j=coeff(pderiv f)(?L-1)*coeff g ?e"
   using coeff_mult_degree_sum[of "pderiv f" g] by (simp only: degree_pderiv)
 have second_product: "coeff(f*pderiv g) ?j=coeff f ?L*coeff(pderiv g)(?e-1)"
   using coeff_mult_degree_sum[of f "pderiv g"] by (simp only: degree_pderiv indices)
 have zero: "coeff g ?j=0" using fdegree by (intro coeff_eq_0) arith
 have coefficient: "A*(of_nat ?L*coeff f ?L*coeff g ?e)-
   B*(coeff f ?L*(of_nat ?e*coeff g ?e))=0"
 proof -
   have raw: "A*coeff(pderiv f*g) ?j-B*coeff(f*pderiv g) ?j=coeff g ?j"
     using arg_cong[where f="\<lambda>p. coeff p ?j", OF equation]
     by simp
   show ?thesis using raw
     by (simp only: first_product second_product derivative_f derivative_g zero)
 qed
 have polynomial_identity: "A*(of_nat ?L*coeff f ?L*coeff g ?e)-
   B*(coeff f ?L*(of_nat ?e*coeff g ?e))=
   (A*of_nat ?L-B*of_nat ?e)*(coeff f ?L*coeff g ?e)"
   by algebra
 have cancelled: "A*of_nat ?L-B*of_nat ?e=0"
   using coefficient topf topg by (simp only: polynomial_identity mult_eq_0_iff; blast)
 show ?thesis using cancelled by simp
qed

end
