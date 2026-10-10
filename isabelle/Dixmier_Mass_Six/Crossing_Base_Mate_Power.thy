theory Crossing_Base_Mate_Power
 imports "Mate_Power_Arithmetic"
  "Bivariate_Prime_Multiplicity"
  "Bivariate_Universal"
begin

definition crossing_primitive_base::"complex\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>complex bivariate" where
 "crossing_primitive_base alpha q rho s=
 ([:[:0,1:]:])*(1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q"

definition crossing_x_zero::"complex bivariate\<Rightarrow>complex poly" where
 "crossing_x_zero F=map_poly (\<lambda>f. poly f 0) F"

lemma crossing_x_zero_hom: "coefficient_hom crossing_x_zero"
 unfolding crossing_x_zero_def[abs_def]
 by (rule coefficient_hom_map_poly[OF coefficient_hom_poly_eval])
lemma crossing_x_zero_mult:
 "crossing_x_zero (F*G)=crossing_x_zero F*crossing_x_zero G"
 using crossing_x_zero_hom by (simp only: coefficient_hom_def; blast)
lemma crossing_x_zero_add:
 "crossing_x_zero (F+G)=crossing_x_zero F+crossing_x_zero G"
 using crossing_x_zero_hom by (simp only: coefficient_hom_def; blast)
lemma crossing_x_zero_power:
 "crossing_x_zero (F^n)=(crossing_x_zero F)^n"
 by (rule coefficient_hom_power[OF crossing_x_zero_hom])
lemma crossing_x_zero_one [simp]: "crossing_x_zero 1=1"
 using crossing_x_zero_hom by (simp only: coefficient_hom_def; blast)
lemma crossing_x_zero_zero [simp]: "crossing_x_zero 0=0"
 using crossing_x_zero_hom by (simp only: coefficient_hom_def; blast)
lemma crossing_x_zero_X [simp]: "crossing_x_zero [:[:0,1:]:]=0"
 by (simp add: crossing_x_zero_def map_poly_pCons)
lemma crossing_x_zero_Y [simp]: "crossing_x_zero ([:0,1:]::complex bivariate)=[:0,1:]"
 by (simp add: crossing_x_zero_def map_poly_pCons)
lemma crossing_x_zero_scalar [simp]: "crossing_x_zero [:[:c:]:]=[:c:]"
 by (simp add: crossing_x_zero_def map_poly_pCons)

lemma crossing_inner_X_prime:
 "prime_elem ([:[:0,1:]:]::complex bivariate)"
 by (rule lift_prime_elem_poly, rule prime_elem_linear_field_poly) simp

lemma crossing_base_inner_factor_x_zero:
 assumes s: "0<s"
 shows "crossing_x_zero ((1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q)=1"
 by (simp only: crossing_x_zero_power crossing_x_zero_add crossing_x_zero_mult
   crossing_x_zero_one crossing_x_zero_X crossing_x_zero_Y crossing_x_zero_scalar zero_power[OF s]; simp)

lemma crossing_base_inner_factor_nonzero:
 assumes s: "0<s"
 shows "((1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q::complex bivariate)\<noteq>0"
proof
 assume zero: "(1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q=0"
 have "crossing_x_zero ((1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q)=0"
   by (simp only: zero crossing_x_zero_zero)
 then show False by (simp only: crossing_base_inner_factor_x_zero[OF s]; simp)
qed

lemma crossing_base_inner_factor_not_X_dvd:
 assumes s: "0<s"
 shows "\<not>([:[:0,1:]:]::complex bivariate) dvd
   (1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q"
proof
 assume divisor: "([:[:0,1:]:]::complex bivariate) dvd
   (1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q"
 then obtain F where F: "(1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q=[:[:0,1:]:]*F"
   by (elim dvdE)
 have "crossing_x_zero ((1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^q)=0"
   by (simp only: F crossing_x_zero_mult crossing_x_zero_X mult_zero_left)
 then show False by (simp only: crossing_base_inner_factor_x_zero[OF s]; simp)
qed

lemma crossing_primitive_base_nonzero:
 assumes s: "0<s"
 shows "crossing_primitive_base alpha q rho s\<noteq>0"
 using crossing_base_inner_factor_nonzero[OF s, where alpha=alpha and q=q and rho=rho]
 by (simp add: crossing_primitive_base_def)

lemma crossing_primitive_base_X_multiplicity:
 assumes s: "0<s"
 shows "multiplicity ([:[:0,1:]:]::complex bivariate) (crossing_primitive_base alpha q rho s)=1"
proof -
 let ?X="[:[:0,1:]:]::complex bivariate"
 let ?H="(1+[:[:alpha:]:]*?X^s*([:0,1:])^rho)^q"
 have X: "?X\<noteq>0" by simp
 have H: "?H\<noteq>0" by (rule crossing_base_inner_factor_nonzero[OF s])
 have zero: "multiplicity ?X ?H=0"
   using prime_elem_multiplicity_eq_zero_iff[OF crossing_inner_X_prime H]
     crossing_base_inner_factor_not_X_dvd[OF s, where alpha=alpha and q=q and rho=rho] by blast
 show ?thesis by (simp only: crossing_primitive_base_def
   prime_elem_multiplicity_mult_distrib[OF crossing_inner_X_prime X H]
   multiplicity_prime[OF crossing_inner_X_prime] zero add_0)
qed

lemma crossingBase_power_ratio_exponent_divides:
 fixes B::"complex bivariate"
 assumes s: "0<s" and B: "B\<noteq>0"
 and power: "B^rho=[:[:c:]:]*(crossing_primitive_base alpha q rho s)^omega"
 shows "rho dvd omega"
proof -
 have c: "c\<noteq>0"
 proof
   assume "c=0"
   then have "B^rho=0" using power by simp
   then show False using B by simp
 qed
 have ratio: "rho*multiplicity ([:[:0,1:]:]::complex bivariate) B=
   omega*multiplicity ([:[:0,1:]:]::complex bivariate) (crossing_primitive_base alpha q rho s)"
   by (rule multiplicity_power_ratio[OF B crossing_primitive_base_nonzero[OF s] c power crossing_inner_X_prime])
 have product: "rho*multiplicity ([:[:0,1:]:]::complex bivariate) B=omega"
   using ratio by (simp only: crossing_primitive_base_X_multiplicity[OF s] mult_1_right)
 show ?thesis by (rule dvdI[of _ _ "multiplicity ([:[:0,1:]:]::complex bivariate) B"])
   (rule sym[OF product])
qed

lemma crossingBase_power_ratio_mate_power:
 fixes B::"complex bivariate"
 assumes s: "0<s" and rho: "0<rho" and omega: "0<omega" and B: "B\<noteq>0"
 and power: "B^rho=[:[:c:]:]*(crossing_primitive_base alpha q rho s)^omega"
 shows "\<exists>j::nat. \<exists>nu::complex. 0<j \<and> omega=rho*j \<and>
   B=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
proof -
 have divides: "rho dvd omega" by (rule crossingBase_power_ratio_exponent_divides[OF s B power])
 obtain j where j: "omega=rho*j" using divides by (elim dvdE)
 have positive: "0<j" using j omega by (cases j) auto
 have same_power: "B^rho=[:[:c:]:]*((crossing_primitive_base alpha q rho s)^j)^rho"
   using power by (simp only: j power_mult mult.commute)
 have base: "(crossing_primitive_base alpha q rho s)^j\<noteq>0"
   using crossing_primitive_base_nonzero[OF s, where alpha=alpha and q=q and rho=rho] by simp
 obtain nu where form: "B=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
   using equal_positive_powers_scalar_ratio[OF rho B base same_power] by blast
 show ?thesis by (rule exI[where x=j], rule exI[where x=nu], intro conjI)
   (rule positive j form)+
qed

lemma crossingBase_not_proper_power:
 fixes S::"complex bivariate"
 assumes s: "0<s" and nu: "nu\<noteq>0" and a: "a\<noteq>0" and k: "2\<le>k" and S: "S\<noteq>0"
 shows "[:[:nu:]:]*crossing_primitive_base alpha q rho s\<noteq>[:[:a:]:]*S^k"
proof
 let ?X="[:[:0,1:]:]::complex bivariate"
 let ?R="[:[:nu:]:]*crossing_primitive_base alpha q rho s"
 assume power: "?R=[:[:a:]:]*S^k"
 have scalar: "([:[:nu:]:]::complex bivariate)\<noteq>0" using nu by simp
 have base: "crossing_primitive_base alpha q rho s\<noteq>0"
   by (rule crossing_primitive_base_nonzero[OF s])
 have R: "?R\<noteq>0" using scalar base by simp
 have order: "multiplicity ?X ?R=1"
   by (simp only: prime_elem_multiplicity_mult_distrib[OF crossing_inner_X_prime scalar base]
     multiplicity_C_ne_zero[OF nu] crossing_primitive_base_X_multiplicity[OF s] add_0)
 have divides: "k dvd multiplicity ?X ?R"
   by (rule multiplicity_dvd_of_scalar_proper_power[OF R _ a power crossing_inner_X_prime]) (use k in arith)
 have "k dvd 1" using divides by (simp only: order)
 then have "k\<le>1" by simp
 then show False using k by arith
qed

end
