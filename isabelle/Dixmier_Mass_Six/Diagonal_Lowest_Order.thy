theory Diagonal_Lowest_Order
 imports Root_Order_Ratio
begin

lemma diagonal_lowest_order_bracket_ne:
 fixes f g::"complex poly" and alpha beta::complex
 assumes m: "0<m" and beta: "beta\<noteq>0" and first: "coeff g m\<noteq>0"
 and low: "\<And>j. j<m \<Longrightarrow> coeff g j=0"
 and diagonal: "alpha=beta*of_nat m"
 shows "[:alpha:]*pderiv f*g-[:beta:]*f*pderiv g\<noteq>g"
proof
 assume equation: "[:alpha:]*pderiv f*g-[:beta:]*f*pderiv g=g"
 obtain k where mk: "m=Suc k" using m by (cases m) auto
 let ?X="[:0,1:]::complex poly"
 have derivative_X: "pderiv ?X=1" by (simp add: pderiv_pCons)
 have scalar: "smult c p=[:c:]*p" for c::complex and p::"complex poly" by simp
 have divides: "monom 1 (Suc k) dvd g"
   using low by (auto simp only: monom_1_dvd_iff' mk)
 obtain q where shape: "g=?X^Suc k*q"
   using divides by (auto simp: dvd_def monom_altdef)
 have monomial: "?X^Suc k=monom 1 (Suc k)" by (simp add: monom_altdef)
 have qzero: "coeff q 0\<noteq>0"
   using first by (simp only: mk shape monomial coeff_monom_mult less_irrefl if_False diff_self diff_self_eq_0 mult_1_left; simp)
 have factor:
   "?X^k*([:alpha:]*?X*pderiv f*q-
     [:beta:]*([:of_nat(Suc k):]*f*q+?X*f*pderiv q))=?X^k*(?X*q)"
 proof -
   have dpower: "pderiv(?X^Suc k)=[:of_nat(Suc k):]*?X^k"
     by (simp only: pderiv_power_Suc derivative_X scalar mult_1_right)
   have expand: "?X^k*([:alpha:]*?X*pderiv f*q-
     [:beta:]*([:of_nat(Suc k):]*f*q+?X*f*pderiv q))=
     [:alpha:]*pderiv f*(?X^Suc k*q)-[:beta:]*f*pderiv(?X^Suc k*q)"
     by (simp only: pderiv_mult dpower; simp only: power_Suc; algebra)
   have right: "g=?X^k*(?X*q)" by (simp only: shape power_Suc; algebra)
   show ?thesis using equation by (simp only: expand shape[symmetric] right)
 qed
 have Xnz: "?X\<noteq>0" by simp
 have Xknz: "?X^k\<noteq>0" using Xnz by simp
 have reduced: "[:alpha:]*?X*pderiv f*q-
   [:beta:]*([:of_nat(Suc k):]*f*q+?X*f*pderiv q)=?X*q"
   by (rule iffD1[OF mult_left_cancel[OF Xknz] factor])
 have at_zero: "beta*of_nat(Suc k)*coeff f 0*coeff q 0=0"
   using arg_cong[where f="\<lambda>p. poly p 0", OF reduced]
   by (simp add: poly_0_coeff_0 coeff_mult_0 mult.assoc)
 have knz: "(of_nat(Suc k)::complex)\<noteq>0" by (simp only: of_nat_eq_0_iff Suc_not_Zero not_False_eq_True)
 have factors: "beta=0 \<or> (of_nat(Suc k)::complex)=0 \<or> coeff f 0=0 \<or> coeff q 0=0"
   using at_zero by (simp only: mult_eq_0_iff; blast)
 have fzero: "coeff f 0=0" using factors beta qzero knz by blast
 have Xdivides: "monom 1 1 dvd f"
   using fzero by (simp add: monom_1_dvd_iff')
 obtain t where tshape: "f=?X*t" using Xdivides by (auto simp: dvd_def monom_altdef)
 have factor2: "?X*([:alpha:]*(t+?X*pderiv t)*q-
   [:beta:]*([:of_nat(Suc k):]*t*q+?X*t*pderiv q))=?X*q"
 proof -
   have expand: "?X*([:alpha:]*(t+?X*pderiv t)*q-
     [:beta:]*([:of_nat(Suc k):]*t*q+?X*t*pderiv q))=
     [:alpha:]*?X*pderiv(?X*t)*q-
     [:beta:]*([:of_nat(Suc k):]*(?X*t)*q+?X*(?X*t)*pderiv q)"
     by (simp only: pderiv_mult derivative_X; algebra)
   show ?thesis using reduced by (simp only: expand tshape)
 qed
 have reduced2: "[:alpha:]*(t+?X*pderiv t)*q-
   [:beta:]*([:of_nat(Suc k):]*t*q+?X*t*pderiv q)=q"
   by (rule iffD1[OF mult_left_cancel[OF Xnz] factor2])
 have last: "alpha*coeff t 0*coeff q 0-beta*of_nat(Suc k)*coeff t 0*coeff q 0=coeff q 0"
   using arg_cong[where f="\<lambda>p. poly p 0", OF reduced2]
   by (simp add: poly_0_coeff_0 coeff_mult_0 mult.assoc)
 have diag: "alpha=beta*of_nat(Suc k)" using diagonal by (simp only: mk)
 have "coeff q 0=0" using last by (simp only: diag mult.assoc diff_self)
 then show False using qzero by contradiction
qed

end
