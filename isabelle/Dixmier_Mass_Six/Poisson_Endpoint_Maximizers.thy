theory Poisson_Endpoint_Maximizers
  imports "Weighted_Product_Components"
begin

text \<open>Native PoissonEndpoints slice at source commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Signed auxiliary weights are
unrestricted. Composition of Weyl operators is not used in these commutative
symbol statements.\<close>

lemma endpoint_biv_monom_diff:
  "biv_monom a i j-biv_monom b i j=biv_monom (a-b) i j"
  for a b :: "complex"
  by (rule biv_eqI) simp
lemma endpoint_biv_monom_neg:
  "-biv_monom a i j=biv_monom (-a) i j" for a :: complex
  by (rule biv_eqI) (simp add: biv_coeff_def biv_monom_def coeff_monom)
lemma endpoint_biv_smult_monom:
  "smult [:c:] (biv_monom a i j)=biv_monom (c*a) i j" for a c :: complex
  by (rule biv_eqI) simp

lemma poisson_monomial_formula:
  fixes a b :: complex
  shows "biv_poisson (biv_monom a i j) (biv_monom b k l)=
    smult [:of_nat j*of_nat k-of_nat i*of_nat l:]
      (biv_monom (a*b) (i+k-1) (j+l-1))"
  by (cases i; cases j; cases k; cases l)
    (simp_all add: biv_poisson_def biv_dx_monom biv_dy_monom biv_mult_monom
      endpoint_biv_monom_diff endpoint_biv_monom_neg endpoint_biv_smult_monom
      algebra_simps)

lemma poisson_monomial_general:
  fixes a b :: complex and d e :: "nat\<times>nat"
  shows "biv_poisson (biv_monom a (fst d) (snd d)) (biv_monom b (fst e) (snd e))=
    smult [:of_nat(snd d)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e):]
      (biv_monom (a*b) (fst d+fst e-1) (snd d+snd e-1))"
  by (rule poisson_monomial_formula)

lemma endpoint_unique_top_component:
  fixes p :: "complex bivariate"
  assumes d: "d\<in>biv_support p"
    and unique: "\<And>x. x\<in>biv_support p \<Longrightarrow>
      pair_weight rho sigma x=pair_weight rho sigma d \<Longrightarrow> x=d"
  shows "weighted_component rho sigma (pair_weight rho sigma d) p=
    biv_monom (biv_coeff p (fst d) (snd d)) (fst d) (snd d)"
proof (rule biv_eqI)
  fix i j
  show "biv_coeff (weighted_component rho sigma (pair_weight rho sigma d) p) i j=
    biv_coeff (biv_monom (biv_coeff p (fst d) (snd d)) (fst d) (snd d)) i j"
  proof (cases "(i,j)=d")
    case True
    then show ?thesis by (cases d) (simp add: weighted_component_coeff)
  next
    case False
    have zero: "pair_weight rho sigma (i,j)=pair_weight rho sigma d \<Longrightarrow>
      biv_coeff p i j=0"
    proof -
      assume weight: "pair_weight rho sigma (i,j)=pair_weight rho sigma d"
      show "biv_coeff p i j=0"
      proof (rule ccontr)
        assume "biv_coeff p i j\<noteq>0"
        then have "(i,j)\<in>biv_support p" by (simp add: biv_support_def)
        from unique[OF this weight] False show False by contradiction
      qed
    qed
    have coords: "\<not>(i=fst d \<and> j=snd d)" using False by (cases d) auto
    show ?thesis using zero coords by (simp add: weighted_component_coeff)
  qed
qed

lemma poisson_unique_maximizers_collinear_of_top_zero:
  fixes p q :: "complex bivariate" and rho sigma :: int
  assumes top_zero: "weighted_component rho sigma
      (pair_weight rho sigma d+pair_weight rho sigma e-(rho+sigma)) (biv_poisson p q)=0"
    and d: "d\<in>biv_support p" and e: "e\<in>biv_support q"
    and dmax: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma d"
    and emax: "\<And>x. x\<in>biv_support q \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma e"
    and dunique: "\<And>x. x\<in>biv_support p \<Longrightarrow>
      pair_weight rho sigma x=pair_weight rho sigma d \<Longrightarrow> x=d"
    and eunique: "\<And>x. x\<in>biv_support q \<Longrightarrow>
      pair_weight rho sigma x=pair_weight rho sigma e \<Longrightarrow> x=e"
  shows "(of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e)=0"
proof -
  have pc: "weighted_component rho sigma (pair_weight rho sigma d) p=
    biv_monom (biv_coeff p (fst d) (snd d)) (fst d) (snd d)"
    by (rule endpoint_unique_top_component[OF d dunique])
  have qc: "weighted_component rho sigma (pair_weight rho sigma e) q=
    biv_monom (biv_coeff q (fst e) (snd e)) (fst e) (snd e)"
    by (rule endpoint_unique_top_component[OF e eunique])
  have mono_zero: "biv_poisson
    (biv_monom (biv_coeff p (fst d) (snd d)) (fst d) (snd d))
    (biv_monom (biv_coeff q (fst e) (snd e)) (fst e) (snd e))=0"
    using poisson_weighted_component_of_bounds[OF dmax emax, where p=p and q=q] top_zero
    by (simp only: pc qc)
  have product_zero: "((of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e))*
    (biv_coeff p (fst d) (snd d)*biv_coeff q (fst e) (snd e))=0"
    using mono_zero by (simp add: poisson_monomial_general endpoint_biv_smult_monom)
  have p_nonzero: "biv_coeff p (fst d) (snd d)\<noteq>0"
    using d by (simp add: biv_support_def)
  have q_nonzero: "biv_coeff q (fst e) (snd e)\<noteq>0"
    using e by (simp add: biv_support_def)
  show ?thesis using product_zero p_nonzero q_nonzero by simp
qed

lemma poisson_unique_maximizers_collinear:
  fixes p q :: "complex bivariate" and rho sigma :: int
  assumes bracket: "biv_poisson p q=0"
    and d: "d\<in>biv_support p" and e: "e\<in>biv_support q"
    and dmax: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma d"
    and emax: "\<And>x. x\<in>biv_support q \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma e"
    and dunique: "\<And>x. x\<in>biv_support p \<Longrightarrow>
      pair_weight rho sigma x=pair_weight rho sigma d \<Longrightarrow> x=d"
    and eunique: "\<And>x. x\<in>biv_support q \<Longrightarrow>
      pair_weight rho sigma x=pair_weight rho sigma e \<Longrightarrow> x=e"
  shows "(of_nat(snd d)::complex)*of_nat(fst e)-of_nat(fst d)*of_nat(snd e)=0"
  by (rule poisson_unique_maximizers_collinear_of_top_zero[OF _ d e dmax emax dunique eunique])
    (simp add: bracket)

end
