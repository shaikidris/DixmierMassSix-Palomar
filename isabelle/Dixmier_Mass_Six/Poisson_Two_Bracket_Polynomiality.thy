theory Poisson_Two_Bracket_Polynomiality
  imports Homogeneous_Centralizer_Nonpositive
begin

lemma poisson_homogeneous_fixed_point_of_two_brackets:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hfne: "f\<noteq>0" and hm: "0<m" and hw: "0<rho+sigma"
    and hbr: "biv_poisson f g\<noteq>0"
    and hsecond: "biv_poisson f (biv_poisson f g)=0"
  shows "\<exists>F. weighted_homogeneous rho sigma (rho+sigma) F \<and> biv_poisson f F=f"
proof (cases "0<m+n-(rho+sigma)")
  case True
  have div: "biv_poisson f g dvd f*g"
    by (rule two_bracket_numerator_divisibility_of_positive_bracket_weight[OF hf hg hfne hm hw hbr hsecond True])
  obtain F where quotient: "f*g=biv_poisson f g*F" using div by (auto simp: dvd_def)
  have fixed: "biv_poisson f F=f \<and> weighted_homogeneous rho sigma (rho+sigma) F"
    by (rule poisson_fixed_point_of_two_brackets_and_division[OF hf hg hbr hsecond quotient[symmetric]])
  show ?thesis using fixed by blast
next
  case False
  then have nonpositive: "m+n-(rho+sigma)\<le>0" by arith
  show ?thesis
    by (rule poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight[OF hf hg hfne hm hbr hsecond nonpositive])
qed

end
