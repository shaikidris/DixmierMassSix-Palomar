theory Strict_Crossing_Face_Shapes
  imports Crossing_Base_Shape
    "One_Sided_Generator_Extraction"
begin

lemma poisson_eq_one_forces_opposite_generator_terms:
  fixes p q::"complex bivariate"
  assumes ell: "0<ell"
    and homogeneous: "\<And>u. u\<in>biv_support p \<Longrightarrow> pair_weight (int ell) (-int d) u=-int d"
    and bracket: "biv_poisson p q=1"
  shows "(0,1)\<in>biv_support p \<and> (1,0)\<in>biv_support q"
proof -
  have not_x: "(1,0)\<notin>biv_support p"
  proof
    assume member: "(1,0)\<in>biv_support p"
    have weight: "int ell= -int d" using homogeneous[OF member] by (simp add: pair_weight_def)
    have "0<int ell" using ell by simp
    moreover have "0\<le>int d" by simp
    ultimately show False using weight by arith
  qed
  have zero_x: "biv_coeff p 1 0=0" using not_x by (simp add: biv_support_def)
  have coeff: "biv_coeff (biv_poisson p q) 0 0=1" using bracket by (simp add: biv_coeff_def)
  have product: "biv_coeff p 0 1*biv_coeff q 1 0=1"
    using coeff by (simp only: poisson_coeff_zero zero_x; simp)
  have y: "biv_coeff p 0 1\<noteq>0" using product by auto
  have x: "biv_coeff q 1 0\<noteq>0" using product by auto
  show ?thesis using y x by (simp add: biv_support_def)
qed

lemma strict_crossing_opposite_generator_face_shapes:
  fixes R F::"complex bivariate" and d ell::nat
  assumes d: "0<d" and direction: "d<ell" and coprime: "coprime ell d"
    and rhom: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight (int ell) (-int d) u=-int d"
    and fhom: "\<And>u. u\<in>biv_support F \<Longrightarrow> pair_weight (int ell) (-int d) u=int ell"
    and bracket: "biv_poisson R F=1"
  shows "\<exists>c e::complex. \<exists>A B::complex poly.
    c\<noteq>0 \<and> e\<noteq>0 \<and> coeff A 0=1 \<and> coeff B 0=1 \<and>
    R=biv_monom c 0 0*(biv_monom 1 0 1*biv_univariate_eval A (biv_monom 1 d ell)) \<and>
    F=biv_monom e 0 0*(biv_monom 1 1 0*biv_univariate_eval B (biv_monom 1 d ell))"
proof -
  have ell: "0<ell" using d direction by arith
  have bases: "(0,1)\<in>biv_support R \<and> (1,0)\<in>biv_support F"
    by (rule poisson_eq_one_forces_opposite_generator_terms[OF ell rhom bracket])
  have rn: "R\<noteq>0" and fn: "F\<noteq>0" using bases by auto
  obtain a b c A where c: "c\<noteq>0" and A: "coeff A 0=1"
    and rray: "\<forall>u\<in>biv_support R. \<exists>t::nat. u=(a+d*t,b+ell*t)"
    and rshape: "R=biv_monom c 0 0*(biv_monom 1 a b*biv_univariate_eval A (biv_monom 1 d ell))"
    using crossing_base_normalized_shape[OF d direction coprime rn rhom] by blast
  obtain a' b' e B where e: "e\<noteq>0" and B: "coeff B 0=1"
    and fray: "\<forall>u\<in>biv_support F. \<exists>t::nat. u=(a'+d*t,b'+ell*t)"
    and fshape: "F=biv_monom e 0 0*(biv_monom 1 a' b'*biv_univariate_eval B (biv_monom 1 d ell))"
    using crossing_base_normalized_shape[OF d direction coprime fn fhom] by blast
  obtain t where t: "(0,1)=(a+d*t,b+ell*t)" using rray bases by blast
  have dt: "d*t=0" using t by (simp add: prod_eq_iff)
  have tz: "t=0" using dt d by simp
  have a: "a=0" and b: "b=1" using t tz by auto
  obtain t' where t': "(1,0)=(a'+d*t',b'+ell*t')" using fray bases by blast
  have et: "ell*t'=0" using t' by (simp add: prod_eq_iff)
  have tz': "t'=0" using et ell by simp
  have a': "a'=1" and b': "b'=0" using t' tz' by auto
  show ?thesis by (intro exI[of _ c] exI[of _ e] exI[of _ A] exI[of _ B])
    (use c e A B rshape fshape in \<open>simp add: a b a' b'\<close>)
qed

end
