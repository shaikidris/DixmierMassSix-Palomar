theory Bivariate_Prime_Multiplicity
  imports Poisson_Prime_Derivative "HOL-Computational_Algebra.Field_as_Ring"
    "HOL-Computational_Algebra.Polynomial_Factorial"
begin

lemma prime_multiplicity_finite:
  fixes R p :: "complex bivariate"
  assumes hR: "R\<noteq>0" and hp: "prime_elem p"
  shows "finite {n. p^n dvd R}"
  by (rule finite_divisor_powers[OF hR]) (use hp in \<open>simp add: prime_elem_def\<close>)

lemma bivariate_scalar_unit:
  assumes "c\<noteq>0"
  shows "is_unit ([:[:c:]:]::complex bivariate)"
proof -
  have product: "([:[:c:]:]::complex bivariate)*[:[:inverse c:]:]=1"
    using assms by (simp add: one_pCons)
  have "([:[:c:]:]::complex bivariate) dvd 1"
    by (rule dvdI[of _ _ "[:[:inverse c:]:]"]) (use product in simp)
  then show ?thesis by simp
qed

lemma multiplicity_C_ne_zero:
  fixes p :: "complex bivariate"
  assumes "c\<noteq>0"
  shows "multiplicity p [:[:c:]:]=0"
  by (rule multiplicity_unit_right[OF bivariate_scalar_unit[OF assms]])

lemma multiplicity_power_ratio:
  fixes B R p :: "complex bivariate"
  assumes hB: "B\<noteq>0" and hR: "R\<noteq>0" and hc: "c\<noteq>0"
    and hpower: "B^m=[:[:c:]:]*R^omega"
    and hp: "prime_elem p"
  shows "m*multiplicity p B=omega*multiplicity p R"
proof -
  have scalar_nz: "([:[:c:]:]::complex bivariate)\<noteq>0" using hc by simp
  have power_nz: "R^omega\<noteq>0" using hR by simp
  have "multiplicity p (B^m)=multiplicity p ([:[:c:]:]*R^omega)"
    using hpower by (rule arg_cong)
  then show ?thesis
    by (simp only: prime_elem_multiplicity_power_distrib[OF hp hB]
      prime_elem_multiplicity_mult_distrib[OF hp scalar_nz power_nz]
      multiplicity_C_ne_zero[OF hc]
      prime_elem_multiplicity_power_distrib[OF hp hR] multiplicity_C_ne_zero[OF hc]
      mult_zero_left add_0)
qed

lemma bivariate_prime_power_decomposition:
  fixes R p :: "complex bivariate"
  assumes hR: "R\<noteq>0" and hp: "prime_elem p"
  obtains F where "R=p^multiplicity p R*F" "\<not>p dvd F"
  by (rule multiplicity_decompose'[OF hR]) (use hp that in \<open>auto simp: prime_elem_def\<close>)

lemma multiplicity_dvd_of_scalar_proper_power:
  fixes R S p :: "complex bivariate"
  assumes hR: "R\<noteq>0" and hd: "1<d" and hc: "c\<noteq>0"
    and hpower: "R=[:[:c:]:]*S^d" and hp: "prime_elem p"
  shows "d dvd multiplicity p R"
proof -
  have hS: "S\<noteq>0" using hR hd hpower by auto
  have scalar_nz: "([:[:c:]:]::complex bivariate)\<noteq>0" using hc by simp
  have power_nz: "S^d\<noteq>0" using hS by simp
  have transport: "multiplicity p R=multiplicity p ([:[:c:]:]*S^d)"
    using hpower by (rule arg_cong)
  have equal: "multiplicity p R=d*multiplicity p S"
    using transport
    by (simp only: prime_elem_multiplicity_mult_distrib[OF hp scalar_nz power_nz]
      prime_elem_multiplicity_power_distrib[OF hp hS] multiplicity_C_ne_zero[OF hc]
      add_0)
  show ?thesis by (simp only: equal) simp
qed

end
