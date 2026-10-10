theory Fourier_Diagonal_Symbol_Algebra
 imports "Fourier_Support_Precursor"
begin

text \<open>Actual commutative substitution X to Y, Y to -X. Outer polynomial
variable is Y, inner variable X. No support-only replacement is used.\<close>

definition diagonalFourierSymbol :: "complex bivariate \<Rightarrow> complex bivariate" where
 "diagonalFourierSymbol = biv_eval (\<lambda>c. [:[:c:]:])
    (biv_monom 1 0 1) (-biv_monom 1 1 0)"
lemma diagonalFourierSymbol_hom:
 "coefficient_hom diagonalFourierSymbol"
 unfolding diagonalFourierSymbol_def
 by (rule biv_eval_hom) (simp add: coefficient_hom_def one_pCons)
lemma diagonalFourierSymbol_add:
 "diagonalFourierSymbol(p+q)=diagonalFourierSymbol p+diagonalFourierSymbol q"
 using diagonalFourierSymbol_hom by (simp add: coefficient_hom_def)
lemma diagonalFourierSymbol_mult:
 "diagonalFourierSymbol(p*q)=diagonalFourierSymbol p*diagonalFourierSymbol q"
 using diagonalFourierSymbol_hom by (simp add: coefficient_hom_def)
lemma diagonalFourierSymbol_monomial:
 "diagonalFourierSymbol(biv_monom a i j)=smult [:(-1)^j:] (biv_monom a j i)"
proof -
 have sign_power: "((-1)::complex bivariate)^n=[:[:(-1)^n:]:]" for n
  by (induction n) (simp_all add: one_pCons)
 have h: "coefficient_hom (\<lambda>c::complex. [:[:c:]:])"
  by (simp add: coefficient_hom_def one_pCons)
 show ?thesis
  by (simp only: diagonalFourierSymbol_def biv_eval_monom[OF h])
    (simp add: biv_monom_def monom_power mult_monom power_minus'
      sign_power smult_monom mult_ac)
qed
lemma diagonalFourierSymbol_smult:
 "diagonalFourierSymbol(smult [:c:] p)=smult [:c:] (diagonalFourierSymbol p)"
proof -
 have scalar_image: "diagonalFourierSymbol [:[:c:]:]=[:[:c:]:]"
  using diagonalFourierSymbol_monomial[of c 0 0]
  by (simp add: biv_monom_def monom_0 one_pCons)
 show ?thesis using diagonalFourierSymbol_mult[of "[:[:c:]:]" p] scalar_image
  by (simp add: mult_pCons_left)
qed
lemma diagonalFourierSymbol_sum:
 "diagonalFourierSymbol(\<Sum>u\<in>S. f u)=(\<Sum>u\<in>S. diagonalFourierSymbol(f u))"
 by (rule coefficient_hom_sum[OF diagonalFourierSymbol_hom])
lemma diagonalFourierSymbol_coeff:
 "biv_coeff (diagonalFourierSymbol p) i j=(-1)^i*biv_coeff p j i"
proof -
 have expand: "diagonalFourierSymbol p=(\<Sum>u\<in>biv_support p.
  smult [:(-1)^snd u:] (biv_monom (biv_coeff p (fst u)(snd u))(snd u)(fst u)))"
  by (subst biv_reconstruct[symmetric, of p])
    (simp only: diagonalFourierSymbol_sum diagonalFourierSymbol_monomial)
 have eq: "(i=snd u \<and> j=fst u)\<longleftrightarrow>u=(j,i)" for u by (cases u) auto
 have delta: "biv_coeff
  (smult [:(-1)^snd u:] (biv_monom (biv_coeff p (fst u)(snd u))(snd u)(fst u))) i j=
  (if u=(j,i) then (-1)^i*biv_coeff p j i else 0)" for u
  by (cases u) (auto simp: eq)
 show ?thesis unfolding expand
  by (simp only: biv_coeff_sum delta sum.delta[OF finite_biv_support])
    (simp add: biv_support_def)
qed
lemma diagonalFourierSymbol_evaluation:
 "map_poly (\<lambda>q. poly q 1) (diagonalFourierSymbol p)=poly p ([:-1:]::complex poly)"
proof -
 let ?E="map_poly (\<lambda>q::complex poly. poly q 1)"
 let ?h="\<lambda>c::complex. [:c:]"
 have h: "coefficient_hom ?h" by (rule constant_polynomial_hom)
 have E: "coefficient_hom ?E"
  by (intro coefficient_hom_map_poly coefficient_hom_poly_eval)
 have F: "coefficient_hom (?E \<circ> diagonalFourierSymbol)"
  by (intro coefficient_hom_comp E diagonalFourierSymbol_hom)
 have scalar_eval: "?E(diagonalFourierSymbol(biv_monom c 0 0))=[:c:]" for c
  by (subst diagonalFourierSymbol_monomial)
    (simp add: biv_monom_def monom_0 one_pCons map_poly_pCons)
 have x_eval: "?E(diagonalFourierSymbol(biv_monom 1 1 0))=[:0,1:]"
  by (subst diagonalFourierSymbol_monomial)
    (simp add: biv_monom_def monom_0 one_pCons monom_Suc map_poly_pCons)
 have y_eval: "?E(diagonalFourierSymbol(biv_monom 1 0 1))=[:-1:]"
  by (subst diagonalFourierSymbol_monomial)
    (simp add: biv_monom_def monom_0 one_pCons monom_Suc map_poly_pCons)
 have map: "?E \<circ> diagonalFourierSymbol=biv_eval ?h [:0,1:] [:-1:]"
  by (rule biv_hom_uniqueness[OF h F])
    (simp_all only: comp_apply scalar_eval x_eval y_eval)
 have original: "(\<lambda>q::complex bivariate. poly q [:-1:])=biv_eval ?h [:0,1:] [:-1:]"
  by (rule biv_hom_uniqueness[OF h coefficient_hom_poly_eval])
    (simp_all add: biv_monom_def poly_monom monom_altdef)
 show ?thesis using fun_cong[OF map, of p] fun_cong[OF original, of p]
  by (simp add: comp_def)
qed

end
