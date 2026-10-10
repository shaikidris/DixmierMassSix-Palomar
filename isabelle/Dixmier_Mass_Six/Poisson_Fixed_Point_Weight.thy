theory Poisson_Fixed_Point_Weight
  imports Poisson_Homogeneous_Weight
begin

definition fixedPointEuler :: "int \<Rightarrow> int \<Rightarrow> complex bivariate \<Rightarrow> complex bivariate" where
  "fixedPointEuler rho sigma F =
    smult [:of_int rho:] (biv_monom 1 1 0*biv_dx F) +
    smult [:of_int sigma:] (biv_monom 1 0 1*biv_dy F)"

lemma joseph_smult_constant:
  "smult [:c:] (F::complex bivariate)=[:[:c:]:]*F"
  by simp

lemma fixedPointEuler_mul:
  "fixedPointEuler rho sigma (F*G)=fixedPointEuler rho sigma F*G + F*fixedPointEuler rho sigma G"
  by (simp only: fixedPointEuler_def biv_dx_mult biv_dy_mult joseph_smult_constant)
    algebra

lemma biv_coeff_monom_left_mult:
  "biv_coeff (biv_monom c a b * (F::complex bivariate)) i j =
    (if j<b then 0 else if i<a then 0 else c*biv_coeff F (i-a) (j-b))"
  by (cases "j<b")
    (simp_all only: biv_coeff_def biv_monom_def coeff_monom_mult if_True if_False coeff_0)

lemma fixedPointEuler_coeff:
  "biv_coeff (fixedPointEuler rho sigma F) i j =
    of_int (pair_weight rho sigma (i,j))*biv_coeff F i j"
  by (simp only: fixedPointEuler_def biv_coeff_add biv_coeff_smult
      biv_coeff_monom_left_mult;
      cases i; cases j)
    (simp_all add: biv_dx_coeff biv_dy_coeff pair_weight_def algebra_simps)

lemma fixedPointEuler_of_homogeneous:
  assumes hom: "weighted_homogeneous rho sigma m F"
  shows "fixedPointEuler rho sigma F=smult [:of_int m:] F"
proof (rule biv_eqI)
  fix i j
  have nz: "biv_coeff F i j\<noteq>0 \<Longrightarrow> pair_weight rho sigma (i,j)=m"
    using hom by (auto simp: weighted_homogeneous_def biv_support_def)
  show "biv_coeff (fixedPointEuler rho sigma F) i j=biv_coeff (smult [:of_int m:] F) i j"
    using nz by (cases "biv_coeff F i j=0") (simp_all add: fixedPointEuler_coeff)
qed

lemma homogeneous_of_fixedPointEuler:
  assumes eq: "fixedPointEuler rho sigma F=smult [:of_int m:] F"
  shows "weighted_homogeneous rho sigma m F"
proof (unfold weighted_homogeneous_def, intro ballI)
  fix u assume mem: "u\<in>biv_support F"
  have nz: "biv_coeff F (fst u) (snd u)\<noteq>0"
    using mem by (simp add: biv_support_def)
  have eqc: "biv_coeff (fixedPointEuler rho sigma F) (fst u) (snd u)=
      biv_coeff (smult [:of_int m:] F) (fst u) (snd u)"
    using eq by simp
  have cast: "(of_int (pair_weight rho sigma u)::complex)=of_int m"
    using eqc nz by (simp add: fixedPointEuler_coeff)
  show "pair_weight rho sigma u=m" using cast by simp
qed

lemma weighted_homogeneous_quotient_of_product:
  fixes f g h F :: "complex bivariate"
  assumes hh: "h\<noteq>0"
    and hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hhw: "weighted_homogeneous rho sigma r h"
    and hdiv: "h*F=f*g"
  shows "weighted_homogeneous rho sigma (m+n-r) F"
proof -
  have Ef: "fixedPointEuler rho sigma f=smult [:of_int m:] f"
    by (rule fixedPointEuler_of_homogeneous[OF hf])
  have Eg: "fixedPointEuler rho sigma g=smult [:of_int n:] g"
    by (rule fixedPointEuler_of_homogeneous[OF hg])
  have Eh: "fixedPointEuler rho sigma h=smult [:of_int r:] h"
    by (rule fixedPointEuler_of_homogeneous[OF hhw])
  have shift: "([:[:of_int (m+n-r):]:]::complex bivariate)=
      [:[:of_int m:]:]+[:[:of_int n:]:]-[:[:of_int r:]:]"
    by simp
  have he: "h*fixedPointEuler rho sigma F = h*smult [:of_int (m+n-r):] F"
  proof -
    have "h*fixedPointEuler rho sigma F =
        fixedPointEuler rho sigma (h*F)-fixedPointEuler rho sigma h*F"
      by (simp only: fixedPointEuler_mul) simp
    also have "... = fixedPointEuler rho sigma (f*g)-smult [:of_int r:] (h*F)"
      by (simp add: hdiv Eh)
    also have "... = smult [:of_int (m+n-r):] (h*F)"
      by (simp only: fixedPointEuler_mul Ef Eg joseph_smult_constant shift hdiv)
        (rule biv_eqI; simp add: algebra_simps)
    also have "... = h*smult [:of_int (m+n-r):] F"
      by (simp only: joseph_smult_constant) algebra
    finally show ?thesis .
  qed
  have "fixedPointEuler rho sigma F=smult [:of_int (m+n-r):] F"
    using he by (simp only: mult_left_cancel[OF hh])
  then show ?thesis by (rule homogeneous_of_fixedPointEuler)
qed

lemma poisson_homogeneous_fixed_point_of_division:
  fixes f g h F :: "complex bivariate"
  assumes hh: "h\<noteq>0"
    and hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hhw: "weighted_homogeneous rho sigma (m+n-(rho+sigma)) h"
    and hbr: "biv_poisson f g=h" and hcentral: "biv_poisson f h=0"
    and hdiv: "h*F=f*g"
  shows "biv_poisson f F=f \<and> weighted_homogeneous rho sigma (rho+sigma) F"
proof
  show "biv_poisson f F=f" by (rule poisson_fixed_point_of_division[OF hh hbr hcentral hdiv])
  have hom: "weighted_homogeneous rho sigma (m+n-(m+n-(rho+sigma))) F"
    by (rule weighted_homogeneous_quotient_of_product[OF hh hf hg hhw hdiv])
  have "m+n-(m+n-(rho+sigma))=rho+sigma" by arith
  then show "weighted_homogeneous rho sigma (rho+sigma) F" using hom by simp
qed

lemma poisson_fixed_point_of_two_brackets_and_division:
  fixes f g F :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hbr: "biv_poisson f g\<noteq>0"
    and hsecond: "biv_poisson f (biv_poisson f g)=0"
    and hdiv: "biv_poisson f g*F=f*g"
  shows "biv_poisson f F=f \<and> weighted_homogeneous rho sigma (rho+sigma) F"
  by (rule poisson_homogeneous_fixed_point_of_division[OF hbr hf hg
      poisson_weighted_homogeneous_signed[OF hf hg] refl hsecond hdiv])

end
