theory Strict_Crossing_Exclusion
  imports Strict_Crossing_Face_Shapes Opposite_Crossing_Bases
begin

lemma strict_crossing_bracket_one_forces_constant_factors:
  fixes R F::"complex bivariate" and d ell::nat
  assumes d: "0<d" and direction: "d<ell" and coprime: "coprime ell d"
    and rhom: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight (int ell) (-int d) u=-int d"
    and fhom: "\<And>u. u\<in>biv_support F \<Longrightarrow> pair_weight (int ell) (-int d) u=int ell"
    and bracket: "biv_poisson R F=1"
  shows "\<exists>A B::complex poly. A\<noteq>0 \<and> B\<noteq>0 \<and>
    R=biv_monom 1 0 1*biv_univariate_eval A (biv_monom 1 d ell) \<and>
    F=biv_monom 1 1 0*biv_univariate_eval B (biv_monom 1 d ell) \<and> degree A=0 \<and> degree B=0"
proof -
  obtain c e A B where c: "c\<noteq>0" and e: "e\<noteq>0" and A: "coeff A 0=1" and B: "coeff B 0=1"
    and rshape: "R=biv_monom c 0 0*(biv_monom 1 0 1*biv_univariate_eval A (biv_monom 1 d ell))"
    and fshape: "F=biv_monom e 0 0*(biv_monom 1 1 0*biv_univariate_eval B (biv_monom 1 d ell))"
    using strict_crossing_opposite_generator_face_shapes[OF d direction coprime rhom fhom bracket] by blast
  let ?A = "[:c:]*A" let ?B = "[:e:]*B"
  have an: "?A\<noteq>0" and bn: "?B\<noteq>0" using c e A B by auto
  have rs: "R=biv_monom 1 0 1*biv_univariate_eval ?A (biv_monom 1 d ell)"
    by (simp add: rshape biv_univariate_eval_mult biv_univariate_eval_smult mult_ac)
  have fs: "F=biv_monom 1 1 0*biv_univariate_eval ?B (biv_monom 1 d ell)"
    by (simp add: fshape biv_univariate_eval_mult biv_univariate_eval_smult mult_ac)
  have br: "biv_poisson (biv_monom 1 0 1*biv_univariate_eval ?A (biv_monom 1 d ell))
    (biv_monom 1 1 0*biv_univariate_eval ?B (biv_monom 1 d ell))=1" using bracket by (simp only: rs fs)
  have ell: "0<ell" using d direction by arith
  have degrees: "degree ?A=0 \<and> degree ?B=0"
    by (rule poisson_opposite_crossing_bases_eq_one_forces_degree_zero[OF ell an bn br])
  show ?thesis by (intro exI[of _ ?A] exI[of _ ?B]) (use an bn rs fs degrees in auto)
qed

lemma strict_crossing_nonmonomial_face_excludes_bracket_one:
  fixes R F::"complex bivariate" and d ell::nat
  assumes d: "0<d" and direction: "d<ell" and coprime: "coprime ell d"
    and rhom: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight (int ell) (-int d) u=-int d"
    and fhom: "\<And>u. u\<in>biv_support F \<Longrightarrow> pair_weight (int ell) (-int d) u=int ell"
    and nonmonomial: "1<card (biv_support R)"
  shows "biv_poisson R F\<noteq>1"
proof
  assume bracket: "biv_poisson R F=1"
  obtain A B where an: "A\<noteq>0" and bn: "B\<noteq>0"
    and rs: "R=biv_monom 1 0 1*biv_univariate_eval A (biv_monom 1 d ell)"
    and fs: "F=biv_monom 1 1 0*biv_univariate_eval B (biv_monom 1 d ell)"
    and adegree: "degree A=0" and bdegree: "degree B=0"
    using strict_crossing_bracket_one_forces_constant_factors[OF d direction coprime rhom fhom bracket] by blast
  have aconstant: "A=[:coeff A 0:]"
  proof (rule poly_eqI)
    fix n show "coeff A n=coeff [:coeff A 0:] n"
      using adegree by (cases n) (simp_all add: coeff_eq_0)
  qed
  have ac: "coeff A 0\<noteq>0" using aconstant an by auto
  have eval_constant: "biv_univariate_eval A (biv_monom 1 d ell)=biv_monom (coeff A 0) 0 0"
    using arg_cong[OF aconstant, where f="\<lambda>p. biv_univariate_eval p (biv_monom 1 d ell)"]
    by (simp only: biv_univariate_eval_const)
  have single: "R=biv_monom (coeff A 0) 0 1"
  proof -
    have "R=biv_monom 1 0 1*biv_monom (coeff A 0) 0 0"
      using rs by (simp only: eval_constant)
    then show ?thesis by (simp only: biv_mult_monom; simp)
  qed
  have support: "biv_support R={(0,1)}"
    using ac by (auto simp: single biv_support_def)
  show False using nonmonomial by (simp add: support)
qed

end
